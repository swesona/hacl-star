/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/nkulatov/new/kremlin/krml -fbuiltin-uint128 -funroll-loops 8 -add-include "TestLib.h" /dist/generic/testlib.c -skip-compilation -no-prefix Hacl.Impl.P256 -bundle Lib.* -bundle Spec.* -bundle Hacl.Impl.P256=Hacl.Impl.P256,Hacl.Spec.P256.*,Hacl.Spec.Curve25519.*,Hacl.Impl.Curve25519.* -library C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.P256.Lemmas -add-include "c/Lib_PrintBuffer.h" -add-include "FStar_UInt_8_16_32_64.h" -tmpdir p256-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Reflection_Types.krml .output/FStar_Reflection_Data.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Mul.krml .output/FStar_Preorder.krml .output/FStar_Calc.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Int.krml .output/FStar_Int16.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_UInt64.krml .output/FStar_Set.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_HyperStack_ST.krml .output/FStar_HyperStack_All.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_Reflection_Const.krml .output/FStar_Char.krml .output/FStar_String.krml .output/FStar_Reflection_Derived.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/FStar_Reflection.krml .output/FStar_Range.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_Reflection_Arith.krml .output/FStar_Tactics_Canon.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/Lib_IntTypes.krml .output/Lib_RawIntTypes.krml .output/Lib_LoopCombinators.krml .output/Spec_Curve25519_Lemmas.krml .output/Lib_Sequence.krml .output/Lib_ByteSequence.krml .output/Spec_Curve25519.krml .output/Hacl_Spec_Curve25519_Field64_Definition.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/LowStar_BufferOps.krml .output/Spec_Loops.krml .output/C_Loops.krml .output/Lib_Loops.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/Hacl_Spec_P256_Definitions.krml .output/Hacl_Impl_Curve25519_Lemmas.krml .output/Hacl_Spec_Curve25519_Field64_Lemmas.krml .output/Hacl_Spec_Curve25519_Field64_Core.krml .output/Hacl_Spec_P256_Lemmas.krml .output/Hacl_Spec_P256_Core.krml .output/Hacl_Spec_P256_SolinasReduction.krml .output/Hacl_Impl_Curve25519_Field64_Core.krml .output/Hacl_Spec_P256_MontgomeryMultiplication.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointDouble.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointAdd.krml .output/Hacl_Spec_P256_Ladder.krml .output/Hacl_Spec_P256_Normalisation.krml .output/Hacl_Impl_P256.krml
  F* version: f2134fe1
  KreMLin version: f534ac02
 */

#include "kremlib.h"
#ifndef __Hacl_Impl_P256_H
#define __Hacl_Impl_P256_H

#include "FStar.h"
#include "TestLib.h"
#include "c/Lib_PrintBuffer.h"
#include "FStar_UInt_8_16_32_64.h"

void pointToDomain(uint64_t *p, uint64_t *result);

void pointFromDomain(uint64_t *p, uint64_t *result);

void point_double(uint64_t *p, uint64_t *result, uint64_t *tempBuffer);

void point_add(uint64_t *p, uint64_t *q, uint64_t *result, uint64_t *tempBuffer);

void norm(uint64_t *p, uint64_t *resultPoint, uint64_t *tempBuffer);

void
montgomery_ladder(
  uint64_t *p,
  uint64_t *q,
  uint32_t scalarSize,
  uint8_t *scalar,
  uint64_t *tempBuffer
);

void
scalarMultiplication(
  uint64_t *p,
  uint64_t *result,
  uint32_t scalarSize,
  uint8_t *scalar,
  uint64_t *tempBuffer
);

#define __Hacl_Impl_P256_H_DEFINED
#endif
