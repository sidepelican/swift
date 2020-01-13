//===--- GenericSpecializer.cpp - Specialization of generic functions -----===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2017 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
// Specialize calls to generic functions by substituting static type
// information.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-generic-specializer"

#include "swift/SIL/OptimizationRemark.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/Utils/Generics.h"
#include "swift/SILOptimizer/Utils/InstOptUtils.h"
#include "swift/SILOptimizer/Utils/SILOptFunctionBuilder.h"
#include "llvm/ADT/SmallVector.h"

using namespace swift;

namespace {

class GenericSpecializer : public SILFunctionTransform {

  bool specializeAppliesInFunction(SILFunction &F);

  /// The entry point to the transformation.
  void run() override {
    SILFunction &F = *getFunction();

    // TODO: We should be able to handle ownership.
    if (F.hasOwnership())
      return;

    LLVM_DEBUG(llvm::dbgs() << "***** GenericSpecializer on function:"
                            << F.getName() << " *****\n");

    if (specializeAppliesInFunction(F))
      invalidateAnalysis(SILAnalysis::InvalidationKind::Everything);
  }

};

} // end anonymous namespace

#include "swift/Demangling/Demangle.h"
bool GenericSpecializer::specializeAppliesInFunction(SILFunction &F) {
  SILOptFunctionBuilder FunctionBuilder(*this);
  DeadInstructionSet DeadApplies;
  llvm::SmallSetVector<SILInstruction *, 8> Applies;
  OptRemark::Emitter ORE(DEBUG_TYPE, F.getModule());

  bool Changed = false;
  for (auto &BB : F) {
    // Collect the applies for this block in reverse order so that we
    // can pop them off the end of our vector and process them in
    // forward order.

      // これの場合でのコメント。
//      sil_scope 1 { loc "generics.swift":6:6 parent @$s8generics1gySbs6UInt16VF : $@convention(thin) (UInt16) -> Bool }
//      sil_scope 2 { loc "generics.swift":6:29 parent 1 }
//      // %0                                             // users: %3, %1
//      bb0(%0 : $UInt16):
//        debug_value %0 : $UInt16, let, name "v", argno 1 // id: %1
//        %2 = alloc_stack $UInt16                        // users: %3, %6, %5
//        store %0 to %2 : $*UInt16                       // id: %3
//        // function_ref f<A>(_:)
//        %4 = function_ref @$s8generics1fySbxSQRzlF : $@convention(thin) <τ_0_0 where τ_0_0 : Equatable> (@in_guaranteed τ_0_0) -> Bool // user: %5
//        %5 = apply %4<UInt16>(%2) : $@convention(thin) <τ_0_0 where τ_0_0 : Equatable> (@in_guaranteed τ_0_0) -> Bool // user: %7
//        dealloc_stack %2 : $*UInt16                     // id: %6
//        return %5 : $Bool                               // id: %7

    for (auto It = BB.rbegin(), End = BB.rend(); It != End; ++It) {  // あとでイテレータ破壊を避けるために逆順に収集
      auto *I = &*It;

      // Skip non-apply instructions, apply instructions with no
      // substitutions, apply instructions where we do not statically
      // know the called function, and apply instructions where we do
      // not have the body of the called function.
      ApplySite Apply = ApplySite::isa(I);
      if (!Apply || !Apply.hasSubstitutions())
        continue;

      auto *Callee = Apply.getReferencedFunctionOrNull();
      if (!Callee)
        continue;
      if (!Callee->isDefinition()) {
        ORE.emit([&]() {
          using namespace OptRemark;
          return RemarkMissed("NoDef", *I)
                 << "Unable to specialize generic function "
                 << NV("Callee", Callee) << " since definition is not visible";
        });
        continue;
      }
        // 1st: 関数呼び出し（apply）のうち、呼び出し先が参照可能なものに関して収集
        //  %5 = apply %4<UInt16>(%2) : $@convention(thin) <τ_0_0 where τ_0_0 : Equatable> (@in_guaranteed τ_0_0) -> Bool // user: %7od
      Applies.insert(Apply.getInstruction());
    }

    // Attempt to specialize each apply we collected, deleting any
    // that we do specialize (along with other instructions we clone
    // in the process of doing so). We pop from the end of the list to
    // avoid tricky iterator invalidation issues.
    while (!Applies.empty()) {
        // 逆順で収集したものを末尾から取り出す　→　先頭から順に最適化を試みる
      auto *I = Applies.pop_back_val();
      auto Apply = ApplySite::isa(I);
      assert(Apply && "Expected an apply!");
      SILFunction *Callee = Apply.getReferencedFunctionOrNull();
      assert(Callee && "Expected to have a known callee");

        // dynamicつきは特殊化しない
      if (!Apply.canOptimize() || !Callee->shouldOptimize())
        continue;

        llvm::dbgs() << "\n";
        llvm::dbgs() << "----------------------------------------------------------------------------\n";
        F.dump();
        llvm::dbgs() << "\n";
        llvm::dbgs() << "specialize: " << swift::Demangle::demangleSymbolAsString(Callee->getName()) << "\n";

      // We have a call that can potentially be specialized, so
      // attempt to do so.
      llvm::SmallVector<SILFunction *, 2> NewFunctions;
      trySpecializeApplyOfGeneric(FunctionBuilder, Apply, DeadApplies,
                                  NewFunctions, ORE);

      // Remove all the now-dead applies. We must do this immediately
      // rather than defer it in order to avoid problems with cloning
      // dead instructions when doing recursive specialization.
      while (!DeadApplies.empty()) { // po DeadApplies.size(); → 1
        auto *AI = DeadApplies.pop_back_val();

        // Remove any applies we are deleting so that we don't attempt
        // to specialize them.
          // 最適化したやつをすぐに消す。
          // いまこうなってる
//          sil_scope 1 { loc "generics.swift":6:6 parent @$s8generics1gySbs6UInt16VF : $@convention(thin) (UInt16) -> Bool }
//          sil_scope 2 { loc "generics.swift":6:29 parent 1 }
//          // %0                                             // users: %3, %1
//          bb0(%0 : $UInt16):
//            debug_value %0 : $UInt16, let, name "v", argno 1 // id: %1
//            %2 = alloc_stack $UInt16                        // users: %6, %3, %9, %8
//            store %0 to %2 : $*UInt16                       // id: %3
//            // function_ref f<A>(_:)
//            %4 = function_ref @$s8generics1fySbxSQRzlF : $@convention(thin) <τ_0_0 where τ_0_0 : Equatable> (@in_guaranteed τ_0_0) -> Bool // user: %8
//            // function_ref specialized f<A>(_:)
//            %5 = function_ref @$s8generics1fySbxSQRzlFs6UInt16V_Tg5 : $@convention(thin) (UInt16) -> Bool // user: %7 // 最適化して生えた特殊化関数。$s8generics1fySbxSQRzlFs6UInt16V_Tg5 ---> generic specialization <Swift.UInt16> of generics.f<A where A: Swift.Equatable>(A) -> Swift.Bool
//            %6 = load %2 : $*UInt16                         // user: %7
//            %7 = apply %5(%6) : $@convention(thin) (UInt16) -> Bool // user: %10
//            %8 = apply %4<UInt16>(%2) : $@convention(thin) <τ_0_0 where τ_0_0 : Equatable> (@in_guaranteed τ_0_0) -> Bool  // ここを消す
//            dealloc_stack %2 : $*UInt16                     // id: %9
//            return %7 : $Bool                               // id: %10

        Applies.remove(AI);

        recursivelyDeleteTriviallyDeadInstructions(AI, true);
        Changed = true;
      }

      // If calling the specialization utility resulted in new functions
      // (as opposed to returning a previous specialization), we need to notify
      // the pass manager so that the new functions get optimized.
      for (SILFunction *NewF : reverse(NewFunctions)) { // po NewFunctions.size(); → 1
          // ここのNewFは特殊化済みのf<UInt16>()
          llvm::dbgs() << "   success: " << swift::Demangle::demangleSymbolAsString(NewF->getName()) << "\n";
        addFunctionToPassManagerWorklist(NewF, Callee);
      }
    }
  }

  return Changed;
}

SILTransform *swift::createGenericSpecializer() {
  return new GenericSpecializer();
}
