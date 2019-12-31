/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/nkulatov/new2/kremlin/kremlin/krml -fbuiltin-uint128 -fnocompound-literals -fc89-scope -fparentheses -fcurly-braces -funroll-loops 4 -warn-error +9 -add-include "kremlib.h" -add-include "FStar_UInt_8_16_32_64.h" /dist/minimal/testlib.c -skip-compilation -no-prefix Hacl.Impl.P256 -bundle Lib.* -bundle Spec.* -bundle C=C.Endianness -bundle Hacl.Hash.SHA2=Hacl.Hash.*,Spec.Hash.* -bundle Hacl.Impl.P256=Hacl.Impl.P256.Arithmetics,Hacl.Impl.P256.PointDouble,Hacl.Impl.P256.PointAdd,Hacl.Impl.P256,Hacl.Impl.P256.MontgomeryMultiplication,Hacl.Impl.P256.LowLevel,Hacl.Impl.LowLevel,Hacl.Impl.SolinasReduction,Hacl.Spec.P256.*,Hacl.Spec.Curve25519.*,Hacl.Impl.Curve25519.* -library C,FStar -drop LowStar,Spec,Prims,Lib,C.Loops.*,Hacl.Spec.P256.Lemmas,Hacl.Spec.P256,Hacl.Spec.ECDSA,Hacl.Spec.Ladder -add-include "c/Lib_PrintBuffer.h" -add-include "FStar_UInt_8_16_32_64.h" -tmpdir ecdsap256-c .output/prims.krml .output/FStar_Pervasives_Native.krml .output/FStar_Pervasives.krml .output/FStar_Squash.krml .output/FStar_Classical.krml .output/FStar_StrongExcludedMiddle.krml .output/FStar_FunctionalExtensionality.krml .output/FStar_List_Tot_Base.krml .output/FStar_List_Tot_Properties.krml .output/FStar_List_Tot.krml .output/FStar_Mul.krml .output/FStar_Math_Lib.krml .output/FStar_Math_Lemmas.krml .output/FStar_Seq_Base.krml .output/FStar_Seq_Properties.krml .output/FStar_Seq.krml .output/FStar_Set.krml .output/FStar_Preorder.krml .output/FStar_Ghost.krml .output/FStar_ErasedLogic.krml .output/FStar_PropositionalExtensionality.krml .output/FStar_PredicateExtensionality.krml .output/FStar_TSet.krml .output/FStar_Monotonic_Heap.krml .output/FStar_Heap.krml .output/FStar_Map.krml .output/FStar_Monotonic_Witnessed.krml .output/FStar_Monotonic_HyperHeap.krml .output/FStar_Monotonic_HyperStack.krml .output/FStar_HyperStack.krml .output/FStar_HyperStack_ST.krml .output/FStar_Calc.krml .output/FStar_BitVector.krml .output/FStar_UInt.krml .output/FStar_UInt32.krml .output/FStar_Universe.krml .output/FStar_GSet.krml .output/FStar_ModifiesGen.krml .output/FStar_Range.krml .output/FStar_Reflection_Types.krml .output/FStar_Tactics_Types.krml .output/FStar_Tactics_Result.krml .output/FStar_Tactics_Effect.krml .output/FStar_Tactics_Util.krml .output/FStar_Reflection_Data.krml .output/FStar_Reflection_Const.krml .output/FStar_Char.krml .output/FStar_Exn.krml .output/FStar_ST.krml .output/FStar_All.krml .output/FStar_List.krml .output/FStar_String.krml .output/FStar_Order.krml .output/FStar_Reflection_Basic.krml .output/FStar_Reflection_Derived.krml .output/FStar_Tactics_Builtins.krml .output/FStar_Reflection_Formula.krml .output/FStar_Reflection_Derived_Lemmas.krml .output/FStar_Reflection.krml .output/FStar_Tactics_Derived.krml .output/FStar_Tactics_Logic.krml .output/FStar_Tactics.krml .output/FStar_BigOps.krml .output/LowStar_Monotonic_Buffer.krml .output/LowStar_Buffer.krml .output/LowStar_BufferOps.krml .output/Spec_Loops.krml .output/FStar_UInt64.krml .output/C_Loops.krml .output/FStar_Int.krml .output/FStar_Int64.krml .output/FStar_Int63.krml .output/FStar_Int32.krml .output/FStar_Int16.krml .output/FStar_Int8.krml .output/FStar_UInt63.krml .output/FStar_UInt16.krml .output/FStar_UInt8.krml .output/FStar_Int_Cast.krml .output/FStar_UInt128.krml .output/FStar_Int_Cast_Full.krml .output/FStar_Int128.krml .output/Lib_IntTypes.krml .output/Lib_Loops.krml .output/Lib_LoopCombinators.krml .output/Lib_RawIntTypes.krml .output/Lib_Sequence.krml .output/Lib_ByteSequence.krml .output/LowStar_ImmutableBuffer.krml .output/Lib_Buffer.krml .output/FStar_HyperStack_All.krml .output/Hacl_Spec_ECDSAP256_Definition.krml .output/Spec_Hash_Definitions.krml .output/Spec_Hash_Lemmas0.krml .output/Spec_Hash_PadFinish.krml .output/Spec_SHA1.krml .output/Spec_MD5.krml .output/Spec_SHA2_Constants.krml .output/Spec_SHA2.krml .output/Spec_Hash.krml .output/Hacl_Spec_P256_Definitions.krml .output/FStar_Reflection_Arith.krml .output/FStar_Tactics_Canon.krml .output/Hacl_Spec_P256_Lemmas.krml .output/Hacl_Spec_P256.krml .output/Hacl_Spec_ECDSA.krml .output/Hacl_Impl_LowLevel.krml .output/Hacl_Impl_ECDSA_MontgomeryMultiplication.krml .output/FStar_Kremlin_Endianness.krml .output/C_Endianness.krml .output/C.krml .output/Lib_ByteBuffer.krml .output/Hacl_Impl_ECDSA_P256SHA256_Common.krml .output/Hacl_Spec_P256_MontgomeryMultiplication.krml .output/Hacl_Impl_P256_LowLevel.krml .output/Hacl_Spec_P256_SolinasReduction.krml .output/Hacl_Impl_SolinasReduction.krml .output/Spec_Hash_Incremental.krml .output/Spec_Hash_Lemmas.krml .output/Hacl_Hash_Lemmas.krml .output/LowStar_Modifies.krml .output/Hacl_Hash_Definitions.krml .output/Hacl_Hash_PadFinish.krml .output/Hacl_Hash_MD.krml .output/Hacl_Math.krml .output/Hacl_Impl_P256_MontgomeryMultiplication.krml .output/Hacl_Impl_P256_Arithmetics.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointDouble.krml .output/Hacl_Spec_P256_MontgomeryMultiplication_PointAdd.krml .output/Hacl_Spec_P256_Ladder.krml .output/Hacl_Impl_ECDSA_MM_Exponent.krml .output/Hacl_Hash_Core_SHA2_Constants.krml .output/Hacl_Hash_Core_SHA2.krml .output/Hacl_Spec_P256_Normalisation.krml .output/Hacl_Impl_P256_PointDouble.krml .output/Hacl_Impl_P256_PointAdd.krml .output/Hacl_Impl_P256.krml .output/Hacl_Hash_SHA2.krml .output/Hacl_Impl_ECDSA_P256SHA256_Verification.krml
  F* version: 0fd6ae12
  KreMLin version: 27ce15c8
 */

#include "Hacl_Impl_ECDSA_P256SHA256_Verification.h"

void Hacl_Impl_ECDSA_P256SHA256_Verification_bufferToJac(uint64_t *p, uint64_t *result)
{
  uint64_t *partPoint = result;
  memcpy(partPoint, p, (uint32_t)8U * sizeof p[0U]);
  result[8U] = (uint64_t)1U;
  result[9U] = (uint64_t)0U;
  result[10U] = (uint64_t)0U;
  result[11U] = (uint64_t)0U;
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_isCoordinateValid(uint64_t *p)
{
  uint64_t tempBuffer[4U] = { 0U };
  uint64_t *x = p;
  uint64_t *y = p + (uint32_t)4U;
  uint64_t
  carryX = Hacl_Impl_LowLevel_sub4_il(x, Hacl_Impl_P256_LowLevel_prime256_buffer, tempBuffer);
  uint64_t
  carryY = Hacl_Impl_LowLevel_sub4_il(y, Hacl_Impl_P256_LowLevel_prime256_buffer, tempBuffer);
  bool lessX = carryX == (uint64_t)1U;
  bool lessY = carryY == (uint64_t)1U;
  bool r = lessX && lessY;
  return r;
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_isOrderCorrect(uint64_t *p, uint64_t *tempBuffer)
{
  uint64_t multResult[12U] = { 0U };
  uint64_t pBuffer[12U] = { 0U };
  memcpy(pBuffer, p, (uint32_t)12U * sizeof p[0U]);
  {
    bool result;
    scalarMultiplicationI(pBuffer,
      multResult,
      Hacl_Impl_ECDSA_MontgomeryMultiplication_order_buffer,
      tempBuffer);
    result = isPointAtInfinity(multResult);
    return result;
  }
}

bool
Hacl_Impl_ECDSA_P256SHA256_Verification_verifyQValidCurvePoint(
  uint64_t *pubKeyAsPoint,
  uint64_t *tempBuffer
)
{
  bool
  coordinatesValid = Hacl_Impl_ECDSA_P256SHA256_Verification_isCoordinateValid(pubKeyAsPoint);
  if (!coordinatesValid)
  {
    return false;
  }
  else
  {
    bool belongsToCurve = isPointOnCurve(pubKeyAsPoint);
    bool
    orderCorrect =
      Hacl_Impl_ECDSA_P256SHA256_Verification_isOrderCorrect(pubKeyAsPoint,
        tempBuffer);
    if (coordinatesValid && belongsToCurve && orderCorrect)
    {
      return true;
    }
    else
    {
      return false;
    }
  }
}

bool Hacl_Impl_ECDSA_P256SHA256_Verification_compare_felem_bool(uint64_t *a, uint64_t *b)
{
  uint64_t a_0 = a[0U];
  uint64_t a_1 = a[1U];
  uint64_t a_2 = a[2U];
  uint64_t a_3 = a[3U];
  uint64_t b_0 = b[0U];
  uint64_t b_1 = b[1U];
  uint64_t b_2 = b[2U];
  uint64_t b_3 = b[3U];
  return a_0 == b_0 && a_1 == b_1 && a_2 == b_2 && a_3 == b_3;
}

bool
Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification_core(
  uint64_t *publicKeyBuffer,
  uint64_t *hashAsFelem,
  uint64_t *r,
  uint64_t *s1,
  uint32_t mLen,
  uint8_t *m,
  uint64_t *xBuffer,
  uint64_t *tempBuffer
)
{
  uint8_t tempBufferU8[64U] = { 0U };
  uint8_t *bufferU1 = tempBufferU8;
  uint8_t *bufferU2 = tempBufferU8 + (uint32_t)32U;
  uint8_t mHash[32U] = { 0U };
  Hacl_Hash_SHA2_hash_256(m, mLen, mHash);
  Hacl_Impl_ECDSA_P256SHA256_Common_toUint64ChangeEndian(mHash, hashAsFelem);
  Hacl_Impl_ECDSA_MontgomeryMultiplication_reduction_prime_2prime_order(hashAsFelem,
    hashAsFelem);
  {
    uint64_t tempBuffer1[12U] = { 0U };
    uint64_t *inverseS = tempBuffer1;
    uint64_t *u11 = tempBuffer1 + (uint32_t)4U;
    uint64_t *u2 = tempBuffer1 + (uint32_t)8U;
    Hacl_Impl_ECDSA_MM_Exponent_fromDomainImpl(s1, inverseS);
    Hacl_Impl_ECDSA_MM_Exponent_montgomery_ladder_exponent(inverseS);
    Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(s1, inverseS, hashAsFelem, u11);
    Hacl_Impl_ECDSA_MM_Exponent_multPowerPartial(s1, inverseS, r, u2);
    Hacl_Impl_ECDSA_P256SHA256_Common_toUint8(u11, bufferU1);
    Hacl_Impl_ECDSA_P256SHA256_Common_toUint8(u2, bufferU2);
    {
      uint64_t pointSum[12U] = { 0U };
      uint64_t points[24U] = { 0U };
      uint64_t *buff = tempBuffer + (uint32_t)12U;
      uint64_t *pointU1G0 = points;
      uint64_t *pointU2Q0 = points + (uint32_t)12U;
      uint64_t *pointU1G;
      uint64_t *pointU2Q;
      bool resultIsPAI;
      uint64_t *xCoordinateSum;
      bool r1;
      secretToPublicWithoutNorm(pointU1G0, bufferU1, tempBuffer);
      scalarMultiplicationWithoutNorm(publicKeyBuffer, pointU2Q0, bufferU2, tempBuffer);
      pointU1G = points;
      pointU2Q = points + (uint32_t)12U;
      Hacl_Impl_P256_PointAdd_point_add(pointU1G, pointU2Q, pointSum, buff);
      norm(pointSum, pointSum, buff);
      resultIsPAI = isPointAtInfinity(pointSum);
      xCoordinateSum = pointSum;
      memcpy(xBuffer, xCoordinateSum, (uint32_t)4U * sizeof xCoordinateSum[0U]);
      r1 = !resultIsPAI;
      return r1;
    }
  }
}

bool
Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification(
  uint64_t *pubKey,
  uint64_t *r,
  uint64_t *s1,
  uint32_t mLen,
  uint8_t *m
)
{
  uint64_t tempBufferU64[120U] = { 0U };
  uint64_t *publicKeyBuffer = tempBufferU64;
  uint64_t *hashAsFelem = tempBufferU64 + (uint32_t)12U;
  uint64_t *tempBuffer = tempBufferU64 + (uint32_t)16U;
  uint64_t *xBuffer = tempBufferU64 + (uint32_t)116U;
  bool publicKeyCorrect;
  bool ite;
  Hacl_Impl_ECDSA_P256SHA256_Verification_bufferToJac(pubKey, publicKeyBuffer);
  publicKeyCorrect =
    Hacl_Impl_ECDSA_P256SHA256_Verification_verifyQValidCurvePoint(publicKeyBuffer,
      tempBuffer);
  if (publicKeyCorrect == false)
  {
    ite = false;
  }
  else
  {
    bool isRCorrect = Hacl_Impl_ECDSA_P256SHA256_Common_isMoreThanZeroLessThanOrderMinusOne(r);
    bool isSCorrect = Hacl_Impl_ECDSA_P256SHA256_Common_isMoreThanZeroLessThanOrderMinusOne(s1);
    bool step1 = isRCorrect && isSCorrect;
    if (step1 == false)
    {
      ite = false;
    }
    else
    {
      bool
      state =
        Hacl_Impl_ECDSA_P256SHA256_Verification_ecdsa_verification_core(publicKeyBuffer,
          hashAsFelem,
          r,
          s1,
          mLen,
          m,
          xBuffer,
          tempBuffer);
      if (state == false)
      {
        ite = false;
      }
      else
      {
        bool result = Hacl_Impl_ECDSA_P256SHA256_Verification_compare_felem_bool(xBuffer, r);
        ite = result;
      }
    }
  }
  return ite;
}

