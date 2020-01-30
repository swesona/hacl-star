/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/aymeric/These/workspaces/2/everest/kremlin/krml -bundle Lib.RandomBuffer.System= -bundle Lib.PrintBuffer= -add-include "evercrypt_targetconfig.h" -bundle Test,Test.*,Hacl.Test.* -ccopts -march=native,-mtune=native -bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] -bundle EverCrypt.Hash+EverCrypt.Hash.Incremental=[rename=EverCrypt_Hash] -bundle Hacl.Impl.SHA3+Hacl.SHA3=[rename=Hacl_SHA3] -bundle Hacl.Chacha20=Hacl.Impl.Chacha20,Hacl.Impl.Chacha20.* -bundle Hacl.Salsa20=Hacl.Impl.Salsa20,Hacl.Impl.Salsa20.*,Hacl.Impl.HSalsa20 -bundle Hacl.Curve25519_64=Hacl.Impl.Curve25519.Field64.Vale -bundle Hacl.Curve25519_64_Slow=Hacl.Impl.Curve25519.Field64.Hacl,Hacl.Spec.Curve25519,Hacl.Spec.Curve25519.\* -bundle Hacl.Curve25519_51=Hacl.Impl.Curve25519.Field51 -bundle Hacl.Impl.Curve25519.\*[rename=Hacl_Curve_Leftovers] -bundle Hacl.Curve25519_64_Local -bundle Hacl.Impl.Chacha20Poly1305 -bundle Hacl.Ed25519=Hacl.Impl.Ed25519.*,Hacl.Impl.BignumQ.Mul,Hacl.Impl.Load56,Hacl.Impl.SHA512.ModQ,Hacl.Impl.Store56,Hacl.Bignum25519 -bundle Hacl.NaCl=Hacl.Impl.SecretBox,Hacl.Impl.Box -bundle MerkleTree.New.Low+MerkleTree.New.Low.Serialization=[rename=MerkleTree] -bundle WasmSupport -bundle EverCrypt.CTR=EverCrypt.CTR.* -bundle Impl.QUIC=Cipher16,Spec.Cipher16,Spec.QUIC -bundle Hacl.Poly1305.Field32xN.Lemmas[rename=Hacl_Lemmas] -drop EverCrypt.TargetConfig -bundle EverCrypt.BCrypt -bundle EverCrypt.OpenSSL -bundle MerkleTree.Spec,MerkleTree.Spec.*,MerkleTree.New.High,MerkleTree.New.High.* -bundle Vale.Stdcalls.*,Vale.Interop,Vale.Interop.*,Vale.Wrapper.X64.*[rename=Vale] -bundle Vale.Inline.X64.*[rename=Vale_Inline] -bundle Vale.*[rename=Unused2] -library Vale.Stdcalls.* -no-prefix Vale.Stdcalls.* -static-header Vale_Inline -library Vale.Inline.X64.Fadd_inline -library Vale.Inline.X64.Fmul_inline -library Vale.Inline.X64.Fswap_inline -library Vale.Inline.X64.Fsqr_inline -no-prefix Vale.Inline.X64.Fadd_inline -no-prefix Vale.Inline.X64.Fmul_inline -no-prefix Vale.Inline.X64.Fswap_inline -no-prefix Vale.Inline.X64.Fsqr_inline -no-prefix EverCrypt.Vale -add-include Hacl_Curve25519_64:"curve25519-inline.h" -no-prefix MerkleTree.New.Low -no-prefix MerkleTree.New.Low.Serialization -bundle Hacl.Impl.Poly1305.Fields -bundle EverCrypt.Spec.* -library EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] -bundle Lib.*[rename=Hacl_Lib] -drop Lib.IntVector.Intrinsics -fparentheses -fno-shadow -fcurly-braces -bundle LowStar.* -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] -bundle Meta.* -minimal -add-include "kremlin/internal/types.h" -add-include "kremlin/lowstar_endianness.h" -add-include <string.h> -add-include "kremlin/internal/target.h" -fbuiltin-uint128 -bundle EverCrypt.AutoConfig2= -bundle Hacl.Poly1305_32,Hacl.Poly1305_128,Hacl.Poly1305_256,Hacl.Impl.Poly1305.Field32xN_32,Hacl.Impl.Poly1305.Field32xN_128,Hacl.Impl.Poly1305.Field32xN_256[rename=Hacl_Poly1305] -bundle Hacl.*[rename=Hacl_Leftovers] -bundle EverCrypt -bundle EverCrypt.Hacl -bundle EverCrypt.Helpers -bundle EverCrypt.Poly1305 -bundle EverCrypt.Chacha20Poly1305 -bundle EverCrypt.AEAD -tmpdir dist/ccf/ -skip-compilation obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_Map.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Mul.krml obj/Vale_Lib_Seqs_s.krml obj/FStar_Preorder.krml obj/FStar_Calc.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_UInt8.krml obj/Vale_Def_Words_s.krml obj/Vale_Def_Words_Four_s.krml obj/Vale_Def_Words_Two_s.krml obj/Vale_Def_Words_Seq_s.krml obj/Vale_Def_Opaque_s.krml obj/Vale_Def_Types_s.krml obj/Vale_X64_Machine_s.krml obj/Vale_Lib_Map16.krml obj/Vale_Def_Prop_s.krml obj/Vale_X64_Flags.krml obj/Vale_AES_AES_s.krml obj/FStar_Float.krml obj/FStar_UInt64.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_Ghost.krml obj/FStar_ErasedLogic.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_PredicateExtensionality.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_IO.krml obj/Vale_Def_PossiblyMonad.krml obj/FStar_List.krml obj/Vale_Lib_Meta.krml obj/Vale_Def_Words_Two.krml obj/Vale_Lib_Seqs.krml obj/Vale_Def_TypesNative_s.krml obj/Vale_Arch_TypesNative.krml obj/Vale_Def_Words_Seq.krml obj/Vale_Arch_Types.krml obj/FStar_UInt16.krml obj/FStar_Monotonic_HyperHeap.krml obj/FStar_Monotonic_HyperStack.krml obj/FStar_HyperStack.krml obj/FStar_HyperStack_ST.krml obj/FStar_Universe.krml obj/FStar_GSet.krml obj/FStar_ModifiesGen.krml obj/FStar_Range.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_Data.krml obj/FStar_Reflection_Const.krml obj/FStar_Char.krml obj/FStar_String.krml obj/FStar_Order.krml obj/FStar_Reflection_Basic.krml obj/FStar_Reflection_Derived.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Reflection_Formula.krml obj/FStar_Reflection_Derived_Lemmas.krml obj/FStar_Reflection.krml obj/FStar_Tactics_Derived.krml obj/FStar_Tactics_Logic.krml obj/FStar_Tactics.krml obj/FStar_BigOps.krml obj/LowStar_Monotonic_Buffer.krml obj/LowStar_BufferView_Down.krml obj/LowStar_BufferView_Up.krml obj/Vale_Interop_Views.krml obj/FStar_Option.krml obj/Vale_Lib_Set.krml obj/Vale_X64_Instruction_s.krml obj/Vale_X64_Bytes_Code_s.krml obj/Vale_Math_Poly2_Defs_s.krml obj/Vale_Math_Poly2_s.krml obj/Vale_Math_Poly2_Bits_s.krml obj/Lib_LoopCombinators.krml obj/FStar_Int.krml obj/FStar_Int64.krml obj/FStar_Int63.krml obj/FStar_Int32.krml obj/FStar_Int16.krml obj/FStar_Int8.krml obj/FStar_UInt63.krml obj/FStar_Int_Cast.krml obj/FStar_UInt128.krml obj/FStar_Int_Cast_Full.krml obj/FStar_Int128.krml obj/Lib_IntTypes.krml obj/Lib_RawIntTypes.krml obj/Lib_Sequence.krml obj/Lib_ByteSequence.krml obj/Spec_Hash_Definitions.krml obj/Spec_Hash_Lemmas0.krml obj/Spec_Hash_PadFinish.krml obj/Spec_Loops.krml obj/Spec_SHA2_Constants.krml obj/Spec_SHA2.krml obj/Vale_X64_CryptoInstructions_s.krml obj/Vale_X64_CPU_Features_s.krml obj/Vale_X64_Instructions_s.krml obj/LowStar_Buffer.krml obj/Vale_Arch_HeapTypes_s.krml obj/Vale_Interop_Types.krml obj/Vale_Arch_MachineHeap_s.krml obj/Vale_Interop_Heap_s.krml obj/LowStar_Modifies.krml obj/LowStar_ModifiesPat.krml obj/LowStar_BufferView.krml obj/Vale_Lib_BufferViewHelpers.krml obj/Vale_Interop.krml obj/Vale_Arch_HeapImpl.krml obj/Vale_Arch_Heap.krml obj/Vale_X64_Machine_Semantics_s.krml obj/LowStar_ImmutableBuffer.krml obj/Vale_Interop_Base.krml obj/Vale_X64_Memory.krml obj/Vale_Arch_MachineHeap.krml obj/Vale_X64_Stack_i.krml obj/Vale_X64_Stack_Sems.krml obj/Vale_X64_BufferViewStore.krml obj/Vale_X64_Memory_Sems.krml obj/Vale_X64_Regs.krml obj/Vale_X64_State.krml obj/Vale_X64_StateLemmas.krml obj/Vale_X64_Lemmas.krml obj/Vale_X64_Print_s.krml obj/Vale_X64_Decls.krml obj/Vale_X64_Taint_Semantics.krml obj/Vale_X64_InsLemmas.krml obj/Vale_X64_QuickCode.krml obj/Vale_X64_InsAes.krml obj/Spec_Chacha20.krml obj/Meta_Attribute.krml obj/LowStar_BufferOps.krml obj/FStar_HyperStack_All.krml obj/FStar_Kremlin_Endianness.krml obj/C_Endianness.krml obj/C.krml obj/C_Loops.krml obj/Lib_Loops.krml obj/Lib_Buffer.krml obj/Lib_ByteBuffer.krml obj/Lib_IntVector_Intrinsics.krml obj/Spec_GaloisField.krml obj/Spec_AES.krml obj/Lib_IntVector.krml obj/Hacl_Spec_Chacha20_Vec.krml obj/Hacl_Spec_Chacha20_Lemmas.krml obj/Lib_Sequence_Lemmas.krml obj/Hacl_Spec_Chacha20_Equiv.krml obj/Hacl_Impl_Chacha20_Core32xN.krml obj/Hacl_Impl_Chacha20_Vec.krml obj/Spec_Poly1305_Lemmas.krml obj/Vale_Curve25519_Fast_lemmas_internal.krml obj/Vale_Curve25519_Fast_defs.krml obj/FStar_Algebra_CommMonoid.krml obj/FStar_Tactics_CanonCommSemiring.krml obj/Vale_Curve25519_FastUtil_helpers.krml obj/Vale_Curve25519_FastHybrid_helpers.krml obj/Vale_Curve25519_Fast_lemmas_external.krml obj/Vale_X64_QuickCodes.krml obj/Vale_X64_InsBasic.krml obj/Vale_X64_InsMem.krml obj/Vale_X64_InsVector.krml obj/Vale_X64_InsStack.krml obj/Vale_Curve25519_X64_FastHybrid.krml obj/Vale_Bignum_Defs.krml obj/Vale_Bignum_X64.krml obj/Vale_Curve25519_FastSqr_helpers.krml obj/Vale_Curve25519_X64_FastSqr.krml obj/Vale_Curve25519_FastMul_helpers.krml obj/Vale_Curve25519_X64_FastMul.krml obj/Vale_Curve25519_X64_FastWide.krml obj/Vale_Curve25519_X64_FastUtil.krml obj/Vale_X64_MemoryAdapters.krml obj/Vale_Interop_Assumptions.krml obj/Vale_Interop_X64.krml obj/Vale_AsLowStar_ValeSig.krml obj/Vale_AsLowStar_LowStarSig.krml obj/Vale_AsLowStar_MemoryHelpers.krml obj/Vale_AsLowStar_Wrapper.krml obj/Vale_Stdcalls_X64_Fadd.krml obj/Vale_Wrapper_X64_Fadd.krml obj/Vale_Math_Poly2_Defs.krml obj/Vale_Math_Poly2.krml obj/Vale_Math_Poly2_Lemmas.krml obj/Vale_Math_Poly2_Bits.krml obj/Vale_Math_Poly2_Words.krml obj/Vale_AES_GF128_s.krml obj/Vale_AES_GF128.krml obj/Vale_AES_OptPublic.krml obj/Vale_AES_X64_GF128_Mul.krml obj/Vale_AES_X64_PolyOps.krml obj/Vale_X64_Stack.krml obj/FStar_BV.krml obj/Vale_Lib_Bv_s.krml obj/Vale_Math_Bits.krml obj/Vale_Lib_Tactics.krml obj/FStar_Reflection_Arith.krml obj/FStar_Tactics_BV.krml obj/Vale_Poly1305_Bitvectors.krml obj/Vale_AES_GCTR_s.krml obj/Vale_AES_GCM_helpers.krml obj/Vale_AES_GCTR.krml obj/Vale_AES_AES256_helpers.krml obj/Vale_AES_X64_AES256.krml obj/Vale_AES_AES_helpers.krml obj/Vale_AES_X64_AES128.krml obj/Vale_AES_X64_AES.krml obj/Vale_AES_GHash_s.krml obj/Vale_AES_GHash.krml obj/Vale_AES_X64_GF128_Init.krml obj/Vale_Transformers_Locations.krml obj/Spec_SHA1.krml obj/Spec_MD5.krml obj/Spec_Agile_Hash.krml obj/Spec_Hash_Incremental.krml obj/Spec_Hash_Lemmas.krml obj/Hacl_Hash_Lemmas.krml obj/Hacl_Hash_Definitions.krml obj/Hacl_Hash_PadFinish.krml obj/Hacl_Hash_MD.krml obj/Spec_SHA2_Lemmas.krml obj/Vale_SHA_SHA_helpers.krml obj/Vale_X64_InsSha.krml obj/Vale_SHA_X64.krml obj/Vale_Stdcalls_X64_Sha.krml obj/Vale_Math_Lemmas_Int.krml obj/FStar_Tactics_Canon.krml obj/Vale_Poly1305_Spec_s.krml obj/Vale_Poly1305_Math.krml obj/Vale_Poly1305_Util.krml obj/Vale_Poly1305_X64.krml obj/Vale_Stdcalls_X64_Poly.krml obj/Vale_Wrapper_X64_Poly.krml obj/FStar_Endianness.krml obj/Vale_Arch_BufferFriend.krml obj/Vale_SHA_Simplify_Sha.krml obj/Vale_Wrapper_X64_Sha.krml obj/Hacl_Hash_Core_SHA2_Constants.krml obj/Hacl_Hash_Core_SHA2.krml obj/Hacl_Hash_SHA2.krml obj/Hacl_Hash_Core_SHA1.krml obj/Hacl_Hash_SHA1.krml obj/Hacl_Hash_Core_MD5.krml obj/Hacl_Hash_MD5.krml obj/C_String.krml obj/C_Failure.krml obj/FStar_Int31.krml obj/FStar_UInt31.krml obj/FStar_Integers.krml obj/EverCrypt_StaticConfig.krml obj/Vale_Lib_Basic.krml obj/Vale_Lib_X64_Cpuid.krml obj/Vale_Lib_X64_Cpuidstdcall.krml obj/Vale_Stdcalls_X64_Cpuid.krml obj/Vale_Wrapper_X64_Cpuid.krml obj/EverCrypt_TargetConfig.krml obj/EverCrypt_AutoConfig2.krml obj/EverCrypt_Helpers.krml obj/EverCrypt_Hash.krml obj/Spec_SHA3_Constants.krml obj/Spec_Curve25519_Lemmas.krml obj/Spec_Curve25519.krml obj/Spec_Ed25519.krml obj/Hacl_Spec_Ed25519_Field56_Definition.krml obj/Hacl_Impl_Ed25519_Field56.krml obj/Hacl_Spec_Curve25519_Field51_Definition.krml obj/Hacl_Impl_Curve25519_Lemmas.krml obj/Hacl_Spec_Curve25519_Field51_Lemmas.krml obj/Hacl_Spec_Curve25519_Field51.krml obj/Hacl_Spec_Curve25519_Field64_Definition.krml obj/Hacl_Spec_Curve25519_Field64_Lemmas.krml obj/Hacl_Spec_Curve25519_Field64_Core.krml obj/Hacl_Spec_Curve25519_Field64.krml obj/Hacl_Impl_Curve25519_Fields_Core.krml obj/Hacl_Impl_Curve25519_Field51.krml obj/Hacl_Impl_Ed25519_Field51.krml obj/Hacl_Spec_Curve25519_Finv.krml obj/Hacl_Impl_Curve25519_Field64.krml obj/Hacl_Impl_Curve25519_Fields.krml obj/FStar_List_Pure_Base.krml obj/FStar_List_Pure_Properties.krml obj/FStar_List_Pure.krml obj/Meta_Interface.krml obj/Hacl_Spec_Curve25519_AddAndDouble.krml obj/Hacl_Impl_Curve25519_AddAndDouble.krml obj/Hacl_Impl_Curve25519_Finv.krml obj/Hacl_Impl_Curve25519_Generic.krml obj/Hacl_Meta_Curve25519.krml obj/Hacl_Curve25519_51.krml obj/Hacl_Curve25519_Finv_Field51.krml obj/Hacl_Bignum25519.krml obj/Hacl_Impl_Ed25519_PointAdd.krml obj/Hacl_Impl_Ed25519_PointDouble.krml obj/Lib_IntTypes_Compatibility.krml obj/Hacl_Impl_Ed25519_SwapConditional.krml obj/Hacl_Impl_Ed25519_Ladder.krml obj/Hacl_Impl_Ed25519_PointCompress.krml obj/Hacl_Impl_Ed25519_SecretExpand.krml obj/Hacl_Impl_Ed25519_SecretToPublic.krml obj/Hacl_Spec_BignumQ_Definitions.krml obj/Hacl_Spec_BignumQ_Lemmas.krml obj/Hacl_Spec_BignumQ_Mul.krml obj/Hacl_Impl_BignumQ_Mul.krml obj/Hacl_Impl_Load56.krml obj/Hacl_Impl_Store56.krml obj/Hacl_Impl_SHA512_ModQ.krml obj/Hacl_Impl_Ed25519_Sign_Steps.krml obj/Hacl_Impl_Ed25519_Sign.krml obj/Hacl_Impl_Ed25519_Sign_Expanded.krml obj/Vale_AES_X64_AESopt2.krml obj/Vale_AES_X64_AESGCM_expected_code.krml obj/Spec_Poly1305.krml obj/Hacl_Spec_Poly1305_Vec.krml obj/Hacl_Spec_Poly1305_Field32xN.krml obj/Hacl_Poly1305_Field32xN_Lemmas.krml obj/Hacl_Impl_Poly1305_Lemmas.krml obj/Hacl_Spec_Poly1305_Field32xN_Lemmas.krml obj/Hacl_Impl_Poly1305_Field32xN.krml obj/Hacl_Spec_Poly1305_Lemmas.krml obj/Hacl_Spec_Poly1305_Equiv.krml obj/Hacl_Impl_Poly1305_Field32xN_256.krml obj/Hacl_Impl_Poly1305_Field32xN_128.krml obj/Hacl_Impl_Poly1305_Field32xN_32.krml obj/Hacl_Impl_Poly1305_Fields.krml obj/Hacl_Impl_Poly1305.krml obj/Spec_Chacha20Poly1305.krml obj/Hacl_Impl_Chacha20Poly1305_PolyCore.krml obj/Hacl_Impl_Chacha20Poly1305.krml obj/Hacl_Meta_Chacha20Poly1305.krml obj/MerkleTree_Spec.krml obj/Hacl_Meta_Chacha20_Vec.krml obj/Hacl_Chacha20_Vec256.krml obj/Hacl_Meta_Poly1305.krml obj/Hacl_Poly1305_256.krml obj/Hacl_Chacha20Poly1305_256.krml obj/Spec_Agile_HMAC.krml obj/Hacl_HMAC.krml obj/Hacl_Impl_Chacha20_Core32.krml obj/Hacl_Impl_Chacha20.krml obj/Hacl_Chacha20.krml obj/Hacl_Poly1305_32.krml obj/Hacl_Chacha20Poly1305_32.krml obj/FStar_Dyn.krml obj/EverCrypt_Vale.krml obj/EverCrypt_Specs.krml obj/EverCrypt_OpenSSL.krml obj/EverCrypt_Hacl.krml obj/EverCrypt_BCrypt.krml obj/EverCrypt_Cipher.krml obj/Vale_Stdcalls_X64_Fswap.krml obj/Vale_Wrapper_X64_Fswap.krml obj/Vale_X64_Print_Inline_s.krml obj/Vale_Inline_X64_Fswap_inline.krml obj/Vale_Stdcalls_X64_Fsqr.krml obj/Vale_Wrapper_X64_Fsqr.krml obj/Vale_Inline_X64_Fsqr_inline.krml obj/Vale_Stdcalls_X64_Fmul.krml obj/Vale_Wrapper_X64_Fmul.krml obj/Vale_Inline_X64_Fmul_inline.krml obj/Vale_Stdcalls_X64_Fsub.krml obj/Vale_Wrapper_X64_Fsub.krml obj/Vale_Inline_X64_Fadd_inline.krml obj/Hacl_Impl_Curve25519_Field64_Vale.krml obj/Hacl_Curve25519_64.krml obj/EverCrypt_Curve25519.krml obj/Hacl_Poly1305_128.krml obj/Vale_Poly1305_Equiv.krml obj/Vale_Poly1305_CallingFromLowStar.krml obj/EverCrypt_Poly1305.krml obj/EverCrypt_HMAC.krml obj/Spec_Agile_HKDF.krml obj/Hacl_HKDF.krml obj/EverCrypt_HKDF.krml obj/EverCrypt.krml obj/Spec_Salsa20.krml obj/Spec_SecretBox.krml obj/Spec_SecretBox_Test.krml obj/Vale_AES_X64_GHash.krml obj/Vale_AES_X64_AESCTR.krml obj/Vale_AES_X64_AESCTRplain.krml obj/Lib_Result.krml obj/Hacl_Impl_Salsa20_Core32.krml obj/Hacl_Impl_Salsa20.krml obj/Hacl_Impl_HSalsa20.krml obj/Hacl_Salsa20.krml obj/Vale_AES_Gcm_simplify.krml obj/Vale_AES_GCM_s.krml obj/Vale_Transformers_BoundedInstructionEffects.krml obj/Vale_Transformers_InstructionReorder.krml obj/Vale_Transformers_Transform.krml obj/Vale_AES_X64_AESopt.krml obj/Vale_AES_X64_AESGCM.krml obj/Vale_AES_X64_GCTR.krml obj/Vale_AES_GCM.krml obj/Vale_AES_X64_GCMencryptOpt.krml obj/Vale_AES_X64_GCMdecryptOpt.krml obj/Vale_Stdcalls_X64_GCMdecryptOpt.krml obj/Vale_Stdcalls_X64_Aes.krml obj/Vale_Wrapper_X64_AES.krml obj/Vale_Wrapper_X64_GCMdecryptOpt.krml obj/Vale_Wrapper_X64_GCMdecryptOpt256.krml obj/Hacl_Chacha20_Vec128.krml obj/Hacl_Chacha20Poly1305_128.krml obj/EverCrypt_Chacha20Poly1305.krml obj/Vale_Stdcalls_X64_GCM_IV.krml obj/Vale_Wrapper_X64_GCM_IV.krml obj/Vale_Stdcalls_X64_GCMencryptOpt.krml obj/Vale_Wrapper_X64_GCMencryptOpt.krml obj/Vale_Wrapper_X64_GCMencryptOpt256.krml obj/Vale_Stdcalls_X64_AesHash.krml obj/Vale_Wrapper_X64_AEShash.krml obj/Spec_Agile_Cipher.krml obj/Spec_Cipher_Expansion.krml obj/EverCrypt_CTR_Keys.krml obj/Spec_Agile_AEAD.krml obj/EverCrypt_Error.krml obj/EverCrypt_AEAD.krml obj/WasmSupport.krml obj/Lib_RandomSequence.krml obj/Vale_Transformers_InstructionReorderSanityChecks.krml obj/Spec_SHA3.krml obj/Hacl_Impl_SHA3.krml obj/LowStar_Vector.krml obj/LowStar_Regional.krml obj/LowStar_RVector.krml obj/LowStar_Regional_Instances.krml obj/TestLib.krml obj/Spec_P256_Definitions.krml obj/Spec_P256_Basic.krml obj/Spec_P256_Lemmas.krml obj/MerkleTree_New_High.krml obj/MerkleTree_New_Low.krml obj/Spec_P256.krml obj/Spec_Curve448_Lemmas.krml obj/Lib_NatMod.krml obj/Spec_Curve448.krml obj/Spec_Agile_DH.krml obj/Spec_Curve448_Test.krml obj/Lib_FixedSequence.krml obj/Spec_SHA2_Fixed.krml obj/Hacl_Impl_Ed25519_Pow2_252m2.krml obj/Hacl_Impl_Ed25519_RecoverX.krml obj/Hacl_Impl_Ed25519_PointDecompress.krml obj/Hacl_Impl_Ed25519_PointEqual.krml obj/Hacl_Impl_Ed25519_Verify.krml obj/Hacl_Ed25519.krml obj/Lib_PrintBuffer.krml obj/Hacl_Test_Ed25519.krml obj/EverCrypt_Hash_Incremental.krml obj/Lib_RandomBuffer_System.krml obj/Spec_SPARKLE.krml obj/Spec_ESCH.krml obj/Test_Vectors_Chacha20Poly1305.krml obj/Spec_Agile_Hash_Incremental.krml obj/Lib_Network.krml obj/Spec_Kyber.krml obj/Spec_SHA2_Test.krml obj/Vale_Test_X64_Args.krml obj/Spec_QUIC.krml obj/Spec_AES128_CBC.krml obj/LowStar_Endianness.krml obj/Lib_PrintSequence.krml obj/Spec_SPARKLE_Test.krml obj/Vale_Test_X64_Vale_memcpy.krml obj/Spec_Poly1305_Test.krml obj/MerkleTree_New_High_Correct_Base.krml obj/MerkleTree_New_High_Correct_Flushing.krml obj/MerkleTree_New_High_Correct_Rhs.krml obj/Test_Vectors_Curve25519.krml obj/Spec_Box.krml obj/Hacl_Impl_SecretBox.krml obj/Hacl_Impl_Box.krml obj/Hacl_NaCl.krml obj/Spec_GF128.krml obj/Spec_GF128_Test.krml obj/Spec_HMAC_Test.krml obj/Vale_Test_X64_Memcpy.krml obj/Hacl_Impl_Curve25519_Field64_Hacl.krml obj/Hacl_Curve25519_64_Slow.krml obj/Spec_Ed25519_Test.krml obj/Spec_Blake2.krml obj/Spec_Blake2_Test.krml obj/Vale_Math_Poly2_Galois_IntTypes.krml obj/Vale_Math_Poly2_Galois.krml obj/Vale_Math_Poly2_Galois_Lemmas.krml obj/Lib_RawBuffer.krml obj/Spec_AES_GCM.krml obj/Spec_Agile_AEAD_Hacl.krml obj/Spec_Defensive_AEAD.krml obj/Vale_Lib_MapTree.krml obj/Test_Vectors_Poly1305.krml obj/Spec_AES_GCM_Test.krml obj/Hacl_SHA3.krml obj/Spec_HKDF_Test.krml obj/Vale_X64_Leakage_s.krml obj/Vale_X64_Leakage_Helpers.krml obj/Vale_X64_Leakage_Ins.krml obj/Vale_X64_Leakage.krml obj/Test_Lowstarize.krml obj/Test_Vectors.krml obj/Spec_Agile_CTR.krml obj/Spec_Blake2_Incremental.krml obj/Spec_AES256.krml obj/Spec_Curve25519_Test.krml obj/Vale_Stdcalls_X64_GCTR.krml obj/Vale_Wrapper_X64_GCTR.krml obj/EverCrypt_CTR.krml obj/Impl_QUIC.krml obj/Lib_ByteSequence_Tuples.krml obj/Spec_Chacha20_Test.krml obj/Spec_AES256_Test.krml obj/Spec_AES256_CBC.krml obj/Vale_Lib_Operator.krml obj/MerkleTree_New_Low_Serialization.krml obj/Spec_HPKE.krml obj/Spec_UPKE.krml obj/Spec_RSAPSS.krml obj/MerkleTree_New_High_Correct_Path.krml obj/MerkleTree_New_High_Correct_Insertion.krml obj/MerkleTree_New_High_Correct.krml obj/Test_Hash.krml obj/Lib_IntVector_Random.krml obj/Spec_Argon2i.krml obj/Hacl_Impl_Curve25519_Field64_Local.krml obj/Spec_RSAPSS_Test.krml obj/Hacl_Test_CSHAKE.krml obj/Spec_Hash_Test.krml obj/Lib_NumericVector.krml obj/Vale_Bignum_Lemmas.krml obj/Test_Vectors_Aes128.krml obj/Hacl_Curve25519_64_Local.krml obj/Hacl_Hash_Agile.krml obj/EverCrypt_Ed25519.krml obj/Hacl_Chacha20_Vec32.krml obj/Spec_Ed448.krml obj/Vale_X64_Xmms.krml obj/Hacl_Test_SHA3.krml obj/Hacl_Test_SHA2.krml obj/Spec_Chacha20Poly1305_Test.krml obj/Spec_Agile_KDF.krml obj/Spec_AES256_CBC_Test.krml obj/Spec_Salsa20_Test.krml obj/Vale_Transformers_DebugPrint.krml obj/Vale_Lib_Lists.krml obj/Spec_Chacha20_Lemmas.krml obj/Vale_FDefMulx_X64.krml obj/Vale_AsLowStar_Test.krml obj/Spec_SHA3_Test.krml obj/Lib_RandomBuffer_Hardware.krml obj/Spec_SHA2_Normal.krml obj/Spec_Hash_KeyedHash.krml obj/Spec_HMAC_KeyedHash.krml obj/Spec_AES_Test.krml obj/Spec_Argon2i_Test.krml obj/Spec_Gimli.krml obj/Test_NoHeap.krml obj/Test_Vectors_Aes128Gcm.krml obj/Spec_Box_Test.krml obj/Vale_X64_Bytes_Semantics.krml obj/Test.krml -silent -ccopt -Wno-unused -warn-error @4-6 -fparentheses Lib_RandomBuffer_System.c -o libevercrypt.a
  F* version: 0ad4b634
  KreMLin version: e324b7e6
 */

#include "Impl_QUIC.h"

Spec_Hash_Definitions_hash_alg
Impl_QUIC___proj__Mkindex__item__hash_alg(Impl_QUIC_index projectee)
{
  return projectee.hash_alg;
}

Spec_Agile_AEAD_alg Impl_QUIC___proj__Mkindex__item__aead_alg(Impl_QUIC_index projectee)
{
  return projectee.aead_alg;
}

bool Impl_QUIC_uu___is_State(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return true;
}

Spec_Hash_Definitions_hash_alg
Impl_QUIC___proj__State__item__the_hash_alg(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.the_hash_alg;
}

Spec_Agile_AEAD_alg
Impl_QUIC___proj__State__item__the_aead_alg(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.the_aead_alg;
}

EverCrypt_AEAD_state_s
*Impl_QUIC___proj__State__item__aead_state(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.aead_state;
}

uint8_t *Impl_QUIC___proj__State__item__iv(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.iv;
}

uint8_t *Impl_QUIC___proj__State__item__hp_key(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.hp_key;
}

uint64_t *Impl_QUIC___proj__State__item__pn(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.pn;
}

EverCrypt_CTR_state_s
*Impl_QUIC___proj__State__item__ctr_state(Impl_QUIC_index i1, Impl_QUIC_state_s projectee)
{
  return projectee.ctr_state;
}

uint8_t Impl_QUIC_add3(uint8_t k1)
{
  if (k1 == (uint8_t)0U)
  {
    return (uint8_t)0U;
  }
  else
  {
    return k1 + (uint8_t)3U;
  }
}

bool Impl_QUIC_uu___is_Short(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Short)
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool Impl_QUIC___proj__Short__item__spin(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Short)
  {
    return projectee.case_Short.spin;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool Impl_QUIC___proj__Short__item__phase(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Short)
  {
    return projectee.case_Short.phase;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t *Impl_QUIC___proj__Short__item__cid(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Short)
  {
    return projectee.case_Short.cid;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t Impl_QUIC___proj__Short__item__cid_len(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Short)
  {
    return projectee.case_Short.cid_len;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool Impl_QUIC_uu___is_Long(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return true;
  }
  else
  {
    return false;
  }
}

uint8_t Impl_QUIC___proj__Long__item__typ(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.typ;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint32_t Impl_QUIC___proj__Long__item__version(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.version;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t *Impl_QUIC___proj__Long__item__dcid(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.dcid;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t Impl_QUIC___proj__Long__item__dcil(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.dcil;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t *Impl_QUIC___proj__Long__item__scid(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.scid;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint8_t Impl_QUIC___proj__Long__item__scil(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.scil;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint32_t Impl_QUIC___proj__Long__item__plain_len(Impl_QUIC_header projectee)
{
  if (projectee.tag == Impl_QUIC_Long)
  {
    return projectee.case_Long.plain_len;
  }
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Spec_Agile_AEAD_alg Impl_QUIC_aead_alg_of_state(Impl_QUIC_state_s *s)
{
  Impl_QUIC_state_s scrut = *s;
  return scrut.the_aead_alg;
}

Spec_Hash_Definitions_hash_alg Impl_QUIC_hash_alg_of_state(Impl_QUIC_state_s *s)
{
  Impl_QUIC_state_s scrut = *s;
  return scrut.the_hash_alg;
}

uint64_t Impl_QUIC_packet_number_of_state(Impl_QUIC_state_s *s)
{
  Impl_QUIC_state_s scrut = *s;
  uint64_t *pn = scrut.pn;
  return *pn;
}

static uint8_t
Impl_QUIC_prefix[11U] =
  {
    (uint8_t)0x74U, (uint8_t)0x6cU, (uint8_t)0x73U, (uint8_t)0x31U, (uint8_t)0x33U, (uint8_t)0x20U,
    (uint8_t)0x71U, (uint8_t)0x75U, (uint8_t)0x69U, (uint8_t)0x63U, (uint8_t)0x20U
  };

static void
Impl_QUIC_derive_secret(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *dst,
  uint8_t dst_len,
  uint8_t *secret1,
  uint8_t *label,
  uint8_t label_len
)
{
  uint32_t label_len32 = (uint32_t)label_len;
  uint32_t dst_len32 = (uint32_t)dst_len;
  uint32_t info_len = (uint32_t)14U + label_len32 + (uint32_t)1U;
  KRML_CHECK_SIZE(sizeof (uint8_t), info_len);
  uint8_t info[info_len];
  memset(info, 0U, info_len * sizeof info[0U]);
  uint8_t *info_lb = info + (uint32_t)1U;
  uint8_t *info_llen = info + (uint32_t)2U;
  uint8_t *info_prefix = info + (uint32_t)3U;
  uint8_t *info_label = info + (uint32_t)14U;
  info_lb[0U] = dst_len;
  info_llen[0U] = label_len + (uint8_t)11U;
  memcpy(info_prefix, Impl_QUIC_prefix, (uint32_t)11U * sizeof Impl_QUIC_prefix[0U]);
  memcpy(info_label, label, label_len32 * sizeof label[0U]);
  uint32_t sw;
  switch (a)
  {
    case Spec_Hash_Definitions_MD5:
      {
        sw = (uint32_t)16U;
        break;
      }
    case Spec_Hash_Definitions_SHA1:
      {
        sw = (uint32_t)20U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_224:
      {
        sw = (uint32_t)28U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_256:
      {
        sw = (uint32_t)32U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_384:
      {
        sw = (uint32_t)48U;
        break;
      }
    case Spec_Hash_Definitions_SHA2_512:
      {
        sw = (uint32_t)64U;
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
  EverCrypt_HKDF_expand(a, dst, secret1, sw, info, info_len, dst_len32);
}

static uint8_t Impl_QUIC_key_len(Spec_Agile_AEAD_alg a)
{
  switch (a)
  {
    case Spec_Agile_AEAD_AES128_GCM:
      {
        return (uint8_t)16U;
      }
    case Spec_Agile_AEAD_AES256_GCM:
      {
        return (uint8_t)32U;
      }
    case Spec_Agile_AEAD_CHACHA20_POLY1305:
      {
        return (uint8_t)32U;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

static uint32_t Impl_QUIC_key_len32(Spec_Agile_AEAD_alg a)
{
  return (uint32_t)Impl_QUIC_key_len(a);
}

static uint8_t Impl_QUIC_label_key[3U] = { (uint8_t)0x6bU, (uint8_t)0x65U, (uint8_t)0x79U };

static uint8_t Impl_QUIC_label_iv[2U] = { (uint8_t)0x69U, (uint8_t)0x76U };

static uint8_t Impl_QUIC_label_hp[2U] = { (uint8_t)0x68U, (uint8_t)0x70U };

EverCrypt_Error_error_code
Impl_QUIC_create_in(
  Impl_QUIC_index i1,
  Impl_QUIC_state_s **dst,
  uint64_t initial_pn,
  uint8_t *traffic_secret
)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), Impl_QUIC_key_len32(i1.aead_alg));
  uint8_t aead_key[Impl_QUIC_key_len32(i1.aead_alg)];
  memset(aead_key, 0U, Impl_QUIC_key_len32(i1.aead_alg) * sizeof aead_key[0U]);
  Impl_QUIC_derive_secret(i1.hash_alg,
    aead_key,
    Impl_QUIC_key_len(i1.aead_alg),
    traffic_secret,
    Impl_QUIC_label_key,
    (uint8_t)3U);
  EverCrypt_AEAD_state_s *aead_state = NULL;
  EverCrypt_Error_error_code ret = EverCrypt_AEAD_create_in(i1.aead_alg, &aead_state, aead_key);
  EverCrypt_CTR_state_s *ctr_state = NULL;
  uint8_t dummy_iv[12U] = { 0U };
  EverCrypt_Error_error_code
  ret_ =
    EverCrypt_CTR_create_in(Spec_Agile_AEAD_cipher_alg_of_supported_alg(i1.aead_alg),
      &ctr_state,
      aead_key,
      dummy_iv,
      (uint32_t)12U,
      (uint32_t)0U);
  switch (ret)
  {
    case EverCrypt_Error_UnsupportedAlgorithm:
      {
        return EverCrypt_Error_UnsupportedAlgorithm;
      }
    case EverCrypt_Error_Success:
      {
        switch (ret_)
        {
          case EverCrypt_Error_UnsupportedAlgorithm:
            {
              return EverCrypt_Error_UnsupportedAlgorithm;
            }
          case EverCrypt_Error_Success:
            {
              EverCrypt_AEAD_state_s *aead_state1 = *&aead_state;
              EverCrypt_CTR_state_s *ctr_state1 = *&ctr_state;
              uint8_t *iv = KRML_HOST_CALLOC((uint32_t)12U, sizeof (uint8_t));
              KRML_CHECK_SIZE(sizeof (uint8_t), Impl_QUIC_key_len32(i1.aead_alg));
              uint8_t
              *hp_key = KRML_HOST_CALLOC(Impl_QUIC_key_len32(i1.aead_alg), sizeof (uint8_t));
              uint64_t *pn = KRML_HOST_MALLOC(sizeof (uint64_t));
              pn[0U] = initial_pn;
              Impl_QUIC_state_s
              s =
                {
                  .the_hash_alg = i1.hash_alg, .the_aead_alg = i1.aead_alg,
                  .aead_state = aead_state1, .iv = iv, .hp_key = hp_key, .pn = pn,
                  .ctr_state = ctr_state1
                };
              KRML_CHECK_SIZE(sizeof (Impl_QUIC_state_s), (uint32_t)1U);
              Impl_QUIC_state_s *s1 = KRML_HOST_MALLOC(sizeof (Impl_QUIC_state_s));
              s1[0U] = s;
              Impl_QUIC_derive_secret(i1.hash_alg,
                iv,
                (uint8_t)12U,
                traffic_secret,
                Impl_QUIC_label_iv,
                (uint8_t)2U);
              Impl_QUIC_derive_secret(i1.hash_alg,
                hp_key,
                Impl_QUIC_key_len(i1.aead_alg),
                traffic_secret,
                Impl_QUIC_label_hp,
                (uint8_t)2U);
              *dst = s1;
              return EverCrypt_Error_Success;
            }
          default:
            {
              KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
              KRML_HOST_EXIT(253U);
            }
        }
        break;
      }
    default:
      {
        KRML_HOST_EPRINTF("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        KRML_HOST_EXIT(253U);
      }
  }
}

EverCrypt_Error_error_code
Impl_QUIC_encrypt(
  Impl_QUIC_state_s *s,
  uint8_t *dst,
  Impl_QUIC_header h1,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t pn_len
)
{
  Impl_QUIC_state_s scrut = *s;
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

uint8_t Impl_QUIC___proj__Mkresult__item__pn_len(Impl_QUIC_result projectee)
{
  return projectee.pn_len;
}

uint64_t Impl_QUIC___proj__Mkresult__item__pn(Impl_QUIC_result projectee)
{
  return projectee.pn;
}

Impl_QUIC_header Impl_QUIC___proj__Mkresult__item__header(Impl_QUIC_result projectee)
{
  return projectee.header;
}

uint32_t Impl_QUIC___proj__Mkresult__item__header_len(Impl_QUIC_result projectee)
{
  return projectee.header_len;
}

uint32_t Impl_QUIC___proj__Mkresult__item__plain_len(Impl_QUIC_result projectee)
{
  return projectee.plain_len;
}

EverCrypt_Error_error_code
Impl_QUIC_decrypt(
  Impl_QUIC_state_s *s,
  Impl_QUIC_result *dst,
  uint8_t *packet,
  uint32_t len,
  uint8_t cid_len1
)
{
  KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n", __FILE__, __LINE__, "");
  KRML_HOST_EXIT(255U);
}

