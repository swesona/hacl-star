/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /home/aymeric/These/workspaces/2/everest/kremlin/krml -bundle Lib.RandomBuffer.System= -bundle Lib.PrintBuffer= -add-include "evercrypt_targetconfig.h" -bundle Test,Test.*,Hacl.Test.* -ccopts -mtune=generic -add-include "libintvector.h" -bundle Hacl.Hash.MD5+Hacl.Hash.Core.MD5+Hacl.Hash.SHA1+Hacl.Hash.Core.SHA1+Hacl.Hash.SHA2+Hacl.Hash.Core.SHA2+Hacl.Hash.Core.SHA2.Constants=Hacl.Hash.*[rename=Hacl_Hash] -bundle EverCrypt.Hash+EverCrypt.Hash.Incremental=[rename=EverCrypt_Hash] -bundle Hacl.Impl.SHA3+Hacl.SHA3=[rename=Hacl_SHA3] -bundle Hacl.Chacha20=Hacl.Impl.Chacha20,Hacl.Impl.Chacha20.* -bundle Hacl.Salsa20=Hacl.Impl.Salsa20,Hacl.Impl.Salsa20.*,Hacl.Impl.HSalsa20 -bundle Hacl.Curve25519_64=Hacl.Impl.Curve25519.Field64.Vale -bundle Hacl.Curve25519_64_Slow=Hacl.Impl.Curve25519.Field64.Hacl,Hacl.Spec.Curve25519,Hacl.Spec.Curve25519.\* -bundle Hacl.Curve25519_51=Hacl.Impl.Curve25519.Field51 -bundle Hacl.Impl.Curve25519.\*[rename=Hacl_Curve_Leftovers] -bundle Hacl.Curve25519_64_Local -bundle Hacl.Impl.Chacha20Poly1305 -bundle Hacl.Ed25519=Hacl.Impl.Ed25519.*,Hacl.Impl.BignumQ.Mul,Hacl.Impl.Load56,Hacl.Impl.SHA512.ModQ,Hacl.Impl.Store56,Hacl.Bignum25519 -bundle Hacl.Poly1305_32=Hacl.Impl.Poly1305.Field32xN_32 -bundle Hacl.Poly1305_128=Hacl.Impl.Poly1305.Field32xN_128 -bundle Hacl.Poly1305_256=Hacl.Impl.Poly1305.Field32xN_256 -bundle Hacl.NaCl=Hacl.Impl.SecretBox,Hacl.Impl.Box -bundle MerkleTree.New.Low+MerkleTree.New.Low.Serialization=[rename=MerkleTree] -bundle WasmSupport -bundle EverCrypt.CTR=EverCrypt.CTR.* -bundle Tutorial -bundle Hacl.Impl.QTesla=QTesla.Params,Hacl.Impl.QTesla.* -bundle Hacl.Frodo.KEM=Frodo.Params,Hacl.Impl.Frodo.*,Hacl.Impl.Matrix,Hacl.Frodo.*,Hacl.Keccak -bundle Hacl.Poly1305.Field32xN.Lemmas[rename=Hacl_Lemmas] -drop EverCrypt.TargetConfig -bundle EverCrypt.BCrypt -bundle EverCrypt.OpenSSL -bundle MerkleTree.Spec,MerkleTree.Spec.*,MerkleTree.New.High,MerkleTree.New.High.* -bundle Vale.Stdcalls.*,Vale.Interop,Vale.Interop.*,Vale.Wrapper.X64.*[rename=Vale] -bundle Vale.Inline.X64.*[rename=Vale_Inline] -bundle Vale.*[rename=Unused2] -library Vale.Stdcalls.* -no-prefix Vale.Stdcalls.* -static-header Vale_Inline -library Vale.Inline.X64.Fadd_inline -library Vale.Inline.X64.Fmul_inline -library Vale.Inline.X64.Fswap_inline -library Vale.Inline.X64.Fsqr_inline -no-prefix Vale.Inline.X64.Fadd_inline -no-prefix Vale.Inline.X64.Fmul_inline -no-prefix Vale.Inline.X64.Fswap_inline -no-prefix Vale.Inline.X64.Fsqr_inline -no-prefix EverCrypt.Vale -add-include Hacl_Curve25519_64:"curve25519-inline.h" -add-include Hacl_Impl_QTesla:"kremlin/fstar_int.h" -no-prefix MerkleTree.New.Low -no-prefix MerkleTree.New.Low.Serialization -bundle Hacl.Impl.Poly1305.Fields -bundle EverCrypt.Spec.* -library EverCrypt.AutoConfig,EverCrypt.OpenSSL,EverCrypt.BCrypt -no-prefix Hacl.Frodo.Random -bundle Hacl.Spec.*,Spec.*[rename=Hacl_Spec] -bundle Lib.*[rename=Hacl_Lib] -drop Lib.IntVector.Intrinsics -fparentheses -fno-shadow -fcurly-braces -bundle LowStar.* -bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*[rename=Hacl_Kremlib] -bundle Meta.* -minimal -add-include "kremlin/internal/types.h" -add-include "kremlin/lowstar_endianness.h" -add-include <string.h> -add-include "kremlin/internal/target.h" -tmpdir dist/portable/ -skip-compilation obj/prims.krml obj/FStar_Pervasives_Native.krml obj/FStar_Pervasives.krml obj/FStar_Squash.krml obj/FStar_Classical.krml obj/FStar_FunctionalExtensionality.krml obj/FStar_Set.krml obj/FStar_Map.krml obj/FStar_StrongExcludedMiddle.krml obj/FStar_List_Tot_Base.krml obj/FStar_List_Tot_Properties.krml obj/FStar_List_Tot.krml obj/FStar_Seq_Base.krml obj/FStar_Seq_Properties.krml obj/FStar_Seq.krml obj/FStar_Mul.krml obj/Vale_Lib_Seqs_s.krml obj/FStar_Preorder.krml obj/FStar_Calc.krml obj/FStar_Math_Lib.krml obj/FStar_Math_Lemmas.krml obj/FStar_BitVector.krml obj/FStar_UInt.krml obj/FStar_UInt32.krml obj/FStar_UInt8.krml obj/Vale_Def_Words_s.krml obj/Vale_Def_Words_Four_s.krml obj/Vale_Def_Words_Two_s.krml obj/Vale_Def_Words_Seq_s.krml obj/Vale_Def_Opaque_s.krml obj/Vale_Def_Types_s.krml obj/Vale_X64_Machine_s.krml obj/Vale_Lib_Map16.krml obj/Vale_Def_Prop_s.krml obj/Vale_X64_Flags.krml obj/Vale_AES_AES_s.krml obj/FStar_Float.krml obj/FStar_UInt64.krml obj/FStar_Exn.krml obj/FStar_Monotonic_Witnessed.krml obj/FStar_Ghost.krml obj/FStar_ErasedLogic.krml obj/FStar_PropositionalExtensionality.krml obj/FStar_PredicateExtensionality.krml obj/FStar_TSet.krml obj/FStar_Monotonic_Heap.krml obj/FStar_Heap.krml obj/FStar_ST.krml obj/FStar_All.krml obj/FStar_IO.krml obj/Vale_Def_PossiblyMonad.krml obj/FStar_List.krml obj/Vale_Lib_Meta.krml obj/Vale_Def_Words_Two.krml obj/Vale_Lib_Seqs.krml obj/Vale_Def_TypesNative_s.krml obj/Vale_Arch_TypesNative.krml obj/Vale_Def_Words_Seq.krml obj/Vale_Arch_Types.krml obj/FStar_UInt16.krml obj/FStar_Monotonic_HyperHeap.krml obj/FStar_Monotonic_HyperStack.krml obj/FStar_HyperStack.krml obj/FStar_HyperStack_ST.krml obj/FStar_Universe.krml obj/FStar_GSet.krml obj/FStar_ModifiesGen.krml obj/FStar_Range.krml obj/FStar_Reflection_Types.krml obj/FStar_Tactics_Types.krml obj/FStar_Tactics_Result.krml obj/FStar_Tactics_Effect.krml obj/FStar_Tactics_Util.krml obj/FStar_Reflection_Data.krml obj/FStar_Reflection_Const.krml obj/FStar_Char.krml obj/FStar_String.krml obj/FStar_Order.krml obj/FStar_Reflection_Basic.krml obj/FStar_Reflection_Derived.krml obj/FStar_Tactics_Builtins.krml obj/FStar_Reflection_Formula.krml obj/FStar_Reflection_Derived_Lemmas.krml obj/FStar_Reflection.krml obj/FStar_Tactics_Derived.krml obj/FStar_Tactics_Logic.krml obj/FStar_Tactics.krml obj/FStar_BigOps.krml obj/LowStar_Monotonic_Buffer.krml obj/LowStar_BufferView_Down.krml obj/LowStar_BufferView_Up.krml obj/Vale_Interop_Views.krml obj/FStar_Option.krml obj/Vale_Lib_Set.krml obj/Vale_X64_Instruction_s.krml obj/Vale_X64_Bytes_Code_s.krml obj/Vale_Math_Poly2_Defs_s.krml obj/Vale_Math_Poly2_s.krml obj/Vale_Math_Poly2_Bits_s.krml obj/Lib_LoopCombinators.krml obj/FStar_Int.krml obj/FStar_Int64.krml obj/FStar_Int63.krml obj/FStar_Int32.krml obj/FStar_Int16.krml obj/FStar_Int8.krml obj/FStar_UInt63.krml obj/FStar_Int_Cast.krml obj/FStar_UInt128.krml obj/FStar_Int_Cast_Full.krml obj/FStar_Int128.krml obj/Lib_IntTypes.krml obj/Lib_RawIntTypes.krml obj/Lib_Sequence.krml obj/Lib_ByteSequence.krml obj/Spec_Hash_Definitions.krml obj/Spec_Hash_Lemmas0.krml obj/Spec_Hash_PadFinish.krml obj/Spec_Loops.krml obj/Spec_SHA2_Constants.krml obj/Spec_SHA2.krml obj/Vale_X64_CryptoInstructions_s.krml obj/Vale_X64_CPU_Features_s.krml obj/Vale_X64_Instructions_s.krml obj/LowStar_Buffer.krml obj/Vale_Arch_HeapTypes_s.krml obj/Vale_Interop_Types.krml obj/Vale_Arch_MachineHeap_s.krml obj/Vale_Interop_Heap_s.krml obj/LowStar_Modifies.krml obj/LowStar_ModifiesPat.krml obj/LowStar_BufferView.krml obj/Vale_Lib_BufferViewHelpers.krml obj/Vale_Interop.krml obj/Vale_Arch_HeapImpl.krml obj/Vale_Arch_Heap.krml obj/Vale_X64_Machine_Semantics_s.krml obj/LowStar_ImmutableBuffer.krml obj/Vale_Interop_Base.krml obj/Vale_X64_Memory.krml obj/Vale_Arch_MachineHeap.krml obj/Vale_X64_Stack_i.krml obj/Vale_X64_Stack_Sems.krml obj/Vale_X64_BufferViewStore.krml obj/Vale_X64_Memory_Sems.krml obj/Vale_X64_Regs.krml obj/Vale_X64_State.krml obj/Vale_X64_StateLemmas.krml obj/Vale_X64_Lemmas.krml obj/Vale_X64_Print_s.krml obj/Vale_X64_Decls.krml obj/Vale_X64_Taint_Semantics.krml obj/Vale_X64_InsLemmas.krml obj/Vale_X64_QuickCode.krml obj/Vale_X64_InsAes.krml obj/Spec_Chacha20.krml obj/Meta_Attribute.krml obj/LowStar_BufferOps.krml obj/C_Loops.krml obj/Lib_Loops.krml obj/FStar_Endianness.krml obj/LowStar_Endianness.krml obj/Lib_Buffer.krml obj/Lib_ByteBuffer.krml obj/FStar_HyperStack_All.krml obj/Lib_IntVector_Intrinsics.krml obj/Spec_GaloisField.krml obj/Spec_AES.krml obj/Lib_IntVector.krml obj/Hacl_Spec_Chacha20_Vec.krml obj/Hacl_Spec_Chacha20_Lemmas.krml obj/Lib_Sequence_Lemmas.krml obj/Hacl_Spec_Chacha20_Equiv.krml obj/Hacl_Impl_Chacha20_Core32xN.krml obj/Hacl_Impl_Chacha20_Vec.krml obj/Spec_Poly1305_Lemmas.krml obj/Vale_Curve25519_Fast_lemmas_internal.krml obj/Vale_Curve25519_Fast_defs.krml obj/FStar_Algebra_CommMonoid.krml obj/FStar_Tactics_CanonCommSemiring.krml obj/Vale_Curve25519_FastUtil_helpers.krml obj/Vale_Curve25519_FastHybrid_helpers.krml obj/Vale_Curve25519_Fast_lemmas_external.krml obj/Vale_X64_QuickCodes.krml obj/Vale_X64_InsBasic.krml obj/Vale_X64_InsMem.krml obj/Vale_X64_InsVector.krml obj/Vale_X64_InsStack.krml obj/Vale_Curve25519_X64_FastHybrid.krml obj/Vale_Bignum_Defs.krml obj/Vale_Bignum_X64.krml obj/Vale_Curve25519_FastSqr_helpers.krml obj/Vale_Curve25519_X64_FastSqr.krml obj/Vale_Curve25519_FastMul_helpers.krml obj/Vale_Curve25519_X64_FastMul.krml obj/Vale_Curve25519_X64_FastWide.krml obj/Vale_Curve25519_X64_FastUtil.krml obj/Vale_X64_MemoryAdapters.krml obj/Vale_Interop_Assumptions.krml obj/Vale_Interop_X64.krml obj/Vale_AsLowStar_ValeSig.krml obj/Vale_AsLowStar_LowStarSig.krml obj/Vale_AsLowStar_MemoryHelpers.krml obj/Vale_AsLowStar_Wrapper.krml obj/Vale_Stdcalls_X64_Fadd.krml obj/Vale_Wrapper_X64_Fadd.krml obj/Vale_Math_Poly2_Defs.krml obj/Vale_Math_Poly2.krml obj/Vale_Math_Poly2_Lemmas.krml obj/Vale_Math_Poly2_Bits.krml obj/Vale_Math_Poly2_Words.krml obj/Vale_AES_GF128_s.krml obj/Vale_AES_GF128.krml obj/Vale_AES_OptPublic.krml obj/Vale_AES_X64_GF128_Mul.krml obj/Vale_AES_X64_PolyOps.krml obj/Vale_X64_Stack.krml obj/FStar_BV.krml obj/Vale_Lib_Bv_s.krml obj/Vale_Math_Bits.krml obj/Vale_Lib_Tactics.krml obj/FStar_Reflection_Arith.krml obj/FStar_Tactics_BV.krml obj/Vale_Poly1305_Bitvectors.krml obj/Vale_AES_GCTR_s.krml obj/Vale_AES_GCM_helpers.krml obj/Vale_AES_GCTR.krml obj/Vale_AES_AES256_helpers.krml obj/Vale_AES_X64_AES256.krml obj/Vale_AES_AES_helpers.krml obj/Vale_AES_X64_AES128.krml obj/Vale_AES_X64_AES.krml obj/Vale_AES_GHash_s.krml obj/Vale_AES_GHash.krml obj/Vale_AES_X64_GF128_Init.krml obj/Vale_Transformers_Locations.krml obj/Spec_SHA1.krml obj/Spec_MD5.krml obj/Spec_Agile_Hash.krml obj/Spec_Hash_Incremental.krml obj/Spec_Hash_Lemmas.krml obj/FStar_Kremlin_Endianness.krml obj/Hacl_Hash_Lemmas.krml obj/Hacl_Hash_Definitions.krml obj/Hacl_Hash_PadFinish.krml obj/Hacl_Hash_MD.krml obj/Spec_SHA2_Lemmas.krml obj/Vale_SHA_SHA_helpers.krml obj/Vale_X64_InsSha.krml obj/Vale_SHA_X64.krml obj/Vale_Stdcalls_X64_Sha.krml obj/Vale_Math_Lemmas_Int.krml obj/FStar_Tactics_Canon.krml obj/Vale_Poly1305_Spec_s.krml obj/Vale_Poly1305_Math.krml obj/Vale_Poly1305_Util.krml obj/Vale_Poly1305_X64.krml obj/Vale_Stdcalls_X64_Poly.krml obj/Vale_Wrapper_X64_Poly.krml obj/Vale_Arch_BufferFriend.krml obj/Vale_SHA_Simplify_Sha.krml obj/Vale_Wrapper_X64_Sha.krml obj/Hacl_Hash_Core_SHA2_Constants.krml obj/Hacl_Hash_Core_SHA2.krml obj/Hacl_Hash_SHA2.krml obj/Hacl_Hash_Core_SHA1.krml obj/Hacl_Hash_SHA1.krml obj/Hacl_Hash_Core_MD5.krml obj/Hacl_Hash_MD5.krml obj/C_Endianness.krml obj/C.krml obj/C_String.krml obj/C_Failure.krml obj/FStar_Int31.krml obj/FStar_UInt31.krml obj/FStar_Integers.krml obj/EverCrypt_StaticConfig.krml obj/Vale_Lib_Basic.krml obj/Vale_Lib_X64_Cpuid.krml obj/Vale_Lib_X64_Cpuidstdcall.krml obj/Vale_Stdcalls_X64_Cpuid.krml obj/Vale_Wrapper_X64_Cpuid.krml obj/EverCrypt_TargetConfig.krml obj/EverCrypt_AutoConfig2.krml obj/EverCrypt_Helpers.krml obj/EverCrypt_Hash.krml obj/Spec_SHA3_Constants.krml obj/Spec_Curve25519_Lemmas.krml obj/Spec_Curve25519.krml obj/Spec_Ed25519.krml obj/Hacl_Spec_Ed25519_Field56_Definition.krml obj/Hacl_Impl_Ed25519_Field56.krml obj/Hacl_Spec_Curve25519_Field51_Definition.krml obj/Hacl_Impl_Curve25519_Lemmas.krml obj/Hacl_Spec_Curve25519_Field51_Lemmas.krml obj/Hacl_Spec_Curve25519_Field51.krml obj/Hacl_Spec_Curve25519_Field64_Definition.krml obj/Hacl_Spec_Curve25519_Field64_Lemmas.krml obj/Hacl_Spec_Curve25519_Field64_Core.krml obj/Hacl_Spec_Curve25519_Field64.krml obj/Hacl_Impl_Curve25519_Fields_Core.krml obj/Hacl_Impl_Curve25519_Field51.krml obj/Hacl_Impl_Ed25519_Field51.krml obj/Hacl_Spec_Curve25519_Finv.krml obj/Hacl_Impl_Curve25519_Field64.krml obj/Hacl_Impl_Curve25519_Fields.krml obj/FStar_List_Pure_Base.krml obj/FStar_List_Pure_Properties.krml obj/FStar_List_Pure.krml obj/Meta_Interface.krml obj/Hacl_Spec_Curve25519_AddAndDouble.krml obj/Hacl_Impl_Curve25519_AddAndDouble.krml obj/Hacl_Impl_Curve25519_Finv.krml obj/Hacl_Impl_Curve25519_Generic.krml obj/Hacl_Meta_Curve25519.krml obj/Hacl_Curve25519_51.krml obj/Hacl_Curve25519_Finv_Field51.krml obj/Hacl_Bignum25519.krml obj/Hacl_Impl_Ed25519_PointAdd.krml obj/Hacl_Impl_Ed25519_PointDouble.krml obj/Lib_IntTypes_Compatibility.krml obj/Hacl_Impl_Ed25519_SwapConditional.krml obj/Hacl_Impl_Ed25519_Ladder.krml obj/Hacl_Impl_Ed25519_PointCompress.krml obj/Hacl_Impl_Ed25519_SecretExpand.krml obj/Hacl_Impl_Ed25519_SecretToPublic.krml obj/Hacl_Spec_BignumQ_Definitions.krml obj/Hacl_Spec_BignumQ_Lemmas.krml obj/Hacl_Spec_BignumQ_Mul.krml obj/Hacl_Impl_BignumQ_Mul.krml obj/Hacl_Impl_Load56.krml obj/Hacl_Impl_Store56.krml obj/Hacl_Impl_SHA512_ModQ.krml obj/Hacl_Impl_Ed25519_Sign_Steps.krml obj/Hacl_Impl_Ed25519_Sign.krml obj/Hacl_Impl_Ed25519_Sign_Expanded.krml obj/Vale_AES_X64_AESopt2.krml obj/Vale_AES_X64_AESGCM_expected_code.krml obj/Spec_Poly1305.krml obj/Hacl_Spec_Poly1305_Vec.krml obj/Hacl_Spec_Poly1305_Field32xN.krml obj/Hacl_Poly1305_Field32xN_Lemmas.krml obj/Hacl_Impl_Poly1305_Lemmas.krml obj/Hacl_Spec_Poly1305_Field32xN_Lemmas.krml obj/Hacl_Impl_Poly1305_Field32xN.krml obj/Hacl_Spec_Poly1305_Lemmas.krml obj/Hacl_Spec_Poly1305_Equiv.krml obj/Hacl_Impl_Poly1305_Field32xN_256.krml obj/Hacl_Impl_Poly1305_Field32xN_128.krml obj/Hacl_Impl_Poly1305_Field32xN_32.krml obj/Hacl_Impl_Poly1305_Fields.krml obj/Hacl_Impl_Poly1305.krml obj/Spec_Chacha20Poly1305.krml obj/Hacl_Impl_Chacha20Poly1305_PolyCore.krml obj/Hacl_Impl_Chacha20Poly1305.krml obj/Hacl_Meta_Chacha20Poly1305.krml obj/MerkleTree_Spec.krml obj/Lib_RandomBuffer_System.krml obj/Spec_SHA3.krml obj/Spec_QTesla_CShake.krml obj/Spec_QTesla_Params.krml obj/Hacl_Impl_SHA3.krml obj/Hacl_SHA3.krml obj/Hacl_Impl_QTesla_ShiftArithmeticLeft.krml obj/Hacl_Impl_QTesla_Heuristic_Parameters.krml obj/Hacl_Impl_QTesla_Constants.krml obj/Hacl_Impl_QTesla_Params.krml obj/Hacl_Impl_QTesla_Lemmas.krml obj/Hacl_Impl_QTesla_Globals.krml obj/Hacl_Impl_QTesla_Platform.krml obj/Hacl_Impl_QTesla_Heuristic_Poly.krml obj/Hacl_Impl_QTesla_Poly.krml obj/Hacl_Impl_QTesla_Heuristic_Pack.krml obj/Hacl_Impl_QTesla_Pack.krml obj/Hacl_Impl_QTesla_Gauss.krml obj/Hacl_Impl_QTesla.krml obj/Hacl_Meta_Chacha20_Vec.krml obj/Hacl_Chacha20_Vec256.krml obj/Hacl_Meta_Poly1305.krml obj/Hacl_Poly1305_256.krml obj/Hacl_Chacha20Poly1305_256.krml obj/Spec_Agile_HMAC.krml obj/Hacl_HMAC.krml obj/Hacl_Impl_Chacha20_Core32.krml obj/Hacl_Impl_Chacha20.krml obj/Hacl_Chacha20.krml obj/Hacl_Poly1305_32.krml obj/Hacl_Chacha20Poly1305_32.krml obj/FStar_Dyn.krml obj/EverCrypt_Vale.krml obj/EverCrypt_Specs.krml obj/EverCrypt_OpenSSL.krml obj/EverCrypt_Hacl.krml obj/EverCrypt_BCrypt.krml obj/EverCrypt_Cipher.krml obj/Vale_Stdcalls_X64_Fswap.krml obj/Vale_Wrapper_X64_Fswap.krml obj/Vale_X64_Print_Inline_s.krml obj/Vale_Inline_X64_Fswap_inline.krml obj/Vale_Stdcalls_X64_Fsqr.krml obj/Vale_Wrapper_X64_Fsqr.krml obj/Vale_Inline_X64_Fsqr_inline.krml obj/Vale_Stdcalls_X64_Fmul.krml obj/Vale_Wrapper_X64_Fmul.krml obj/Vale_Inline_X64_Fmul_inline.krml obj/Vale_Stdcalls_X64_Fsub.krml obj/Vale_Wrapper_X64_Fsub.krml obj/Vale_Inline_X64_Fadd_inline.krml obj/Hacl_Impl_Curve25519_Field64_Vale.krml obj/Hacl_Curve25519_64.krml obj/EverCrypt_Curve25519.krml obj/Hacl_Poly1305_128.krml obj/Vale_Poly1305_Equiv.krml obj/Vale_Poly1305_CallingFromLowStar.krml obj/EverCrypt_Poly1305.krml obj/EverCrypt_HMAC.krml obj/Spec_Agile_HKDF.krml obj/Hacl_HKDF.krml obj/EverCrypt_HKDF.krml obj/EverCrypt.krml obj/Spec_Salsa20.krml obj/Spec_SecretBox.krml obj/Spec_SecretBox_Test.krml obj/Vale_AES_X64_GHash.krml obj/Vale_AES_X64_AESCTR.krml obj/Vale_AES_X64_AESCTRplain.krml obj/Lib_Result.krml obj/Hacl_Impl_Salsa20_Core32.krml obj/Hacl_Impl_Salsa20.krml obj/Hacl_Impl_HSalsa20.krml obj/Hacl_Salsa20.krml obj/Vale_AES_Gcm_simplify.krml obj/Vale_AES_GCM_s.krml obj/Vale_Transformers_BoundedInstructionEffects.krml obj/Vale_Transformers_InstructionReorder.krml obj/Vale_Transformers_Transform.krml obj/Vale_AES_X64_AESopt.krml obj/Vale_AES_X64_AESGCM.krml obj/Vale_AES_X64_GCTR.krml obj/Vale_AES_GCM.krml obj/Vale_AES_X64_GCMencryptOpt.krml obj/Vale_AES_X64_GCMdecryptOpt.krml obj/Vale_Stdcalls_X64_GCMdecryptOpt.krml obj/Vale_Stdcalls_X64_Aes.krml obj/Vale_Wrapper_X64_AES.krml obj/Vale_Wrapper_X64_GCMdecryptOpt.krml obj/Vale_Wrapper_X64_GCMdecryptOpt256.krml obj/Hacl_Chacha20_Vec128.krml obj/Hacl_Chacha20Poly1305_128.krml obj/EverCrypt_Chacha20Poly1305.krml obj/Vale_Stdcalls_X64_GCM_IV.krml obj/Vale_Wrapper_X64_GCM_IV.krml obj/Vale_Stdcalls_X64_GCMencryptOpt.krml obj/Vale_Wrapper_X64_GCMencryptOpt.krml obj/Vale_Wrapper_X64_GCMencryptOpt256.krml obj/Vale_Stdcalls_X64_AesHash.krml obj/Vale_Wrapper_X64_AEShash.krml obj/Spec_Agile_Cipher.krml obj/Spec_Cipher_Expansion.krml obj/EverCrypt_CTR_Keys.krml obj/Spec_Agile_AEAD.krml obj/EverCrypt_Error.krml obj/EverCrypt_AEAD.krml obj/WasmSupport.krml obj/Spec_P256_Definitions.krml obj/Spec_P256_Basic.krml obj/Spec_P256_Lemmas.krml obj/Spec_P256.krml obj/Spec_Curve448_Lemmas.krml obj/Lib_NatMod.krml obj/Spec_Curve448.krml obj/Spec_Agile_DH.krml obj/Spec_Agile_HPKE.krml obj/Hacl_Impl_Generic_HKDF.krml obj/Lib_RandomSequence.krml obj/Vale_Transformers_InstructionReorderSanityChecks.krml obj/Hacl_Impl_Generic_Hash.krml obj/Hacl_Impl_Generic_AEAD.krml obj/Hacl_Impl_Generic_DH.krml obj/Hacl_Impl_HPKE.krml obj/Hacl_Meta_HPKE.krml obj/Hacl_Impl_Instantiate_AEAD.krml obj/Hacl_HPKE_Curve51_CP256_SHA256.krml obj/LowStar_Vector.krml obj/LowStar_Regional.krml obj/LowStar_RVector.krml obj/LowStar_Regional_Instances.krml obj/Hacl_AES128.krml obj/TestLib.krml obj/MerkleTree_New_High.krml obj/MerkleTree_New_Low.krml obj/Spec_Frodo_Random.krml obj/Spec_Frodo_Lemmas.krml obj/Spec_Matrix.krml obj/Spec_Frodo_Gen.krml obj/Frodo_Params.krml obj/Spec_Frodo_Sample.krml obj/Spec_Frodo_Pack.krml obj/Spec_Frodo_Params.krml obj/Spec_Frodo_Encode.krml obj/Spec_Frodo_KEM_Encaps.krml obj/Spec_Curve448_Test.krml obj/Lib_FixedSequence.krml obj/Spec_SHA2_Fixed.krml obj/Hacl_Keccak.krml obj/Hacl_Impl_Matrix.krml obj/Hacl_Impl_Frodo_Gen.krml obj/Hacl_Impl_Ed25519_Pow2_252m2.krml obj/Hacl_Impl_Ed25519_RecoverX.krml obj/Hacl_Impl_Ed25519_PointDecompress.krml obj/Hacl_Impl_Ed25519_PointEqual.krml obj/Hacl_Impl_Ed25519_Verify.krml obj/Hacl_Ed25519.krml obj/Lib_PrintBuffer.krml obj/Hacl_Test_Ed25519.krml obj/Spec_Frodo_KEM_Decaps.krml obj/Spec_Frodo_KEM_KeyGen.krml obj/Spec_Frodo_Test.krml obj/Spec_Frodo_KEM.krml obj/EverCrypt_Hash_Incremental.krml obj/Hacl_HPKE_Curve64_CP32_SHA512.krml obj/Spec_SPARKLE.krml obj/Spec_ESCH.krml obj/Hacl_Impl_Frodo_Params.krml obj/Hacl_Impl_Frodo_Sample.krml obj/Test_Vectors_Chacha20Poly1305.krml obj/Spec_Agile_Hash_Incremental.krml obj/Lib_Network.krml obj/Spec_Kyber.krml obj/Hacl_HPKE_Curve64_CP32_SHA256.krml obj/Spec_SHA2_Test.krml obj/Vale_Test_X64_Args.krml obj/Spec_AES128_CBC.krml obj/Lib_PrintSequence.krml obj/Spec_SPARKLE_Test.krml obj/Vale_Test_X64_Vale_memcpy.krml obj/Spec_Poly1305_Test.krml obj/MerkleTree_New_High_Correct_Base.krml obj/MerkleTree_New_High_Correct_Flushing.krml obj/MerkleTree_New_High_Correct_Rhs.krml obj/Test_Vectors_Curve25519.krml obj/Spec_Box.krml obj/Hacl_Impl_SecretBox.krml obj/Hacl_Impl_Box.krml obj/Hacl_NaCl.krml obj/Spec_GF128.krml obj/Spec_GF128_Test.krml obj/Spec_HMAC_Test.krml obj/Vale_Test_X64_Memcpy.krml obj/Hacl_Impl_Curve25519_Field64_Hacl.krml obj/Hacl_Curve25519_64_Slow.krml obj/Hacl_HPKE_Curve51_CP32_SHA512.krml obj/Spec_Ed25519_Test.krml obj/Spec_Blake2.krml obj/Spec_Blake2_Test.krml obj/Vale_Math_Poly2_Galois_IntTypes.krml obj/Vale_Math_Poly2_Galois.krml obj/Vale_Math_Poly2_Galois_Lemmas.krml obj/Lib_RawBuffer.krml obj/Spec_AES_GCM.krml obj/Spec_Agile_AEAD_Hacl.krml obj/Spec_Defensive_AEAD.krml obj/Vale_Lib_MapTree.krml obj/Test_Vectors_Poly1305.krml obj/Spec_AES_GCM_Test.krml obj/Spec_HKDF_Test.krml obj/Hacl_HPKE_Curve64_CP256_SHA256.krml obj/Hacl_HPKE_Curve51_CP32_SHA256.krml obj/Vale_X64_Leakage_s.krml obj/Vale_X64_Leakage_Helpers.krml obj/Vale_X64_Leakage_Ins.krml obj/Vale_X64_Leakage.krml obj/Test_Lowstarize.krml obj/Test_Vectors.krml obj/Spec_Agile_CTR.krml obj/Hacl_HPKE_Curve64_CP128_SHA256.krml obj/Hacl_HPKE_Curve51_CP128_SHA256.krml obj/Spec_Blake2_Incremental.krml obj/Spec_AES256.krml obj/Spec_Curve25519_Test.krml obj/Hacl_HPKE_Curve64_CP256_SHA512.krml obj/Spec_QTesla_Random.krml obj/Lib_ByteSequence_Tuples.krml obj/Spec_Chacha20_Test.krml obj/Hacl_Impl_Frodo_Pack.krml obj/Spec_AES256_Test.krml obj/Spec_AES256_CBC.krml obj/Hacl_HPKE_Curve51_CP256_SHA512.krml obj/Vale_Lib_Operator.krml obj/MerkleTree_New_Low_Serialization.krml obj/Hacl_Frodo_Random.krml obj/Lib_Memzero.krml obj/Hacl_Impl_Frodo_KEM.krml obj/Hacl_Impl_Frodo_KEM_KeyGen.krml obj/Spec_UPKE.krml obj/Spec_RSAPSS.krml obj/MerkleTree_New_High_Correct_Path.krml obj/MerkleTree_New_High_Correct_Insertion.krml obj/MerkleTree_New_High_Correct.krml obj/Test_Hash.krml obj/Lib_IntVector_Random.krml obj/Spec_Argon2i.krml obj/Hacl_HPKE_Curve64_CP128_SHA512.krml obj/Hacl_Impl_Curve25519_Field64_Local.krml obj/Spec_RSAPSS_Test.krml obj/Hacl_Test_CSHAKE.krml obj/Spec_Hash_Test.krml obj/Lib_NumericVector.krml obj/Hacl_Impl_QTesla_TargetConfig.krml obj/Vale_Stdcalls_X64_GCTR.krml obj/Vale_Wrapper_X64_GCTR.krml obj/Vale_Bignum_Lemmas.krml obj/Hacl_Impl_Frodo_Encode.krml obj/Hacl_Impl_Frodo_KEM_Encaps.krml obj/Hacl_Impl_Frodo_KEM_Decaps.krml obj/Hacl_Frodo_KEM.krml obj/Test_Vectors_Aes128.krml obj/Hacl_Curve25519_64_Local.krml obj/Hacl_Hash_Agile.krml obj/EverCrypt_Ed25519.krml obj/Hacl_Chacha20_Vec32.krml obj/Spec_Ed448.krml obj/Vale_X64_Xmms.krml obj/Hacl_Test_SHA3.krml obj/Hacl_Test_SHA2.krml obj/Spec_Chacha20Poly1305_Test.krml obj/Spec_Agile_KDF.krml obj/Spec_AES256_CBC_Test.krml obj/Spec_Salsa20_Test.krml obj/Vale_Transformers_DebugPrint.krml obj/Vale_Lib_Lists.krml obj/Spec_Chacha20_Lemmas.krml obj/Vale_FDefMulx_X64.krml obj/Hacl_Test_QTesla.krml obj/Vale_AsLowStar_Test.krml obj/Spec_SHA3_Test.krml obj/Lib_RandomBuffer_Hardware.krml obj/Spec_SHA2_Normal.krml obj/Spec_Hash_KeyedHash.krml obj/Spec_HMAC_KeyedHash.krml obj/Spec_AES_Test.krml obj/Spec_Argon2i_Test.krml obj/Spec_Gimli.krml obj/Test_NoHeap.krml obj/EverCrypt_CTR.krml obj/Hacl_HPKE_Curve51_CP128_SHA512.krml obj/Test_Vectors_Aes128Gcm.krml obj/Spec_Box_Test.krml obj/Vale_X64_Bytes_Semantics.krml obj/Tutorial.krml obj/Test.krml -silent -ccopt -Wno-unused -warn-error @4-6 -fparentheses Hacl_AES.c Lib_RandomBuffer_System.c Lib_Memzero.c Lib_PrintBuffer.c evercrypt_vale_stubs.c -o libevercrypt.a
  F* version: 182fa4da
  KreMLin version: 88253438
 */

#include "Hacl_Curve25519_64.h"

inline static uint64_t
Hacl_Impl_Curve25519_Field64_Vale_add1(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  return add1_inline(out1, f1, f2);
  #else
  uint64_t scrut = add1(out1, f1, f2);
  return scrut;
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fadd(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fadd_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fadd_(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsub(uint64_t *out1, uint64_t *f1, uint64_t *f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsub_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fsub_(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul(
  uint64_t *out1,
  uint64_t *f1,
  uint64_t *f2,
  uint64_t *tmp
)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul_inline(tmp, f1, out1, f2);
  #else
  uint64_t uu____0 = fmul_(tmp, f1, out1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul2(
  uint64_t *out1,
  uint64_t *f1,
  uint64_t *f2,
  uint64_t *tmp
)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul2_inline(tmp, f1, out1, f2);
  #else
  uint64_t uu____0 = fmul2(tmp, f1, out1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fmul1(uint64_t *out1, uint64_t *f1, uint64_t f2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fmul1_inline(out1, f1, f2);
  #else
  uint64_t uu____0 = fmul1(out1, f1, f2);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsqr(uint64_t *out1, uint64_t *f1, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr_inline(tmp, f1, out1);
  #else
  uint64_t uu____0 = fsqr(tmp, f1, out1);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_fsqr2(uint64_t *out1, uint64_t *f, uint64_t *tmp)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  fsqr2_inline(tmp, f, out1);
  #else
  uint64_t uu____0 = fsqr2(tmp, f, out1);
  #endif
}

inline static void
Hacl_Impl_Curve25519_Field64_Vale_cswap2(uint64_t bit, uint64_t *p1, uint64_t *p2)
{
  #if EVERCRYPT_TARGETCONFIG_GCC
  cswap2_inline(bit, p1, p2);
  #else
  uint64_t uu____0 = cswap2(bit, p1, p2);
  #endif
}

static uint8_t
Hacl_Curve25519_64_g25519[32U] =
  {
    (uint8_t)9U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U,
    (uint8_t)0U, (uint8_t)0U, (uint8_t)0U, (uint8_t)0U
  };

static void
Hacl_Curve25519_64_point_add_and_double(uint64_t *q, uint64_t *p01_tmp1, uint64_t *tmp2)
{
  uint64_t *nq = p01_tmp1;
  uint64_t *nq_p1 = p01_tmp1 + (uint32_t)8U;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  uint64_t *x1 = q;
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *z3 = nq_p1 + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  Hacl_Impl_Curve25519_Field64_Vale_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(b, x2, z2);
  uint64_t *x3 = nq_p1;
  uint64_t *z31 = nq_p1 + (uint32_t)4U;
  uint64_t *d0 = dc;
  uint64_t *c0 = dc + (uint32_t)4U;
  Hacl_Impl_Curve25519_Field64_Vale_fadd(c0, x3, z31);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(d0, x3, z31);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(dc, dc, ab, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(x3, d0, c0);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(z31, d0, c0);
  uint64_t *a1 = tmp1;
  uint64_t *b1 = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab1 = tmp1;
  uint64_t *dc1 = tmp1 + (uint32_t)8U;
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(nq_p1, nq_p1, tmp2);
  a1[0U] = c[0U];
  a1[1U] = c[1U];
  a1[2U] = c[2U];
  a1[3U] = c[3U];
  Hacl_Impl_Curve25519_Field64_Vale_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field64_Vale_fmul1(b1, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(b1, b1, d);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(nq, dc1, ab1, tmp2);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(z3, z3, x1, tmp2);
}

static void Hacl_Curve25519_64_point_double(uint64_t *nq, uint64_t *tmp1, uint64_t *tmp2)
{
  uint64_t *x2 = nq;
  uint64_t *z2 = nq + (uint32_t)4U;
  uint64_t *a = tmp1;
  uint64_t *b = tmp1 + (uint32_t)4U;
  uint64_t *d = tmp1 + (uint32_t)8U;
  uint64_t *c = tmp1 + (uint32_t)12U;
  uint64_t *ab = tmp1;
  uint64_t *dc = tmp1 + (uint32_t)8U;
  Hacl_Impl_Curve25519_Field64_Vale_fadd(a, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsub(b, x2, z2);
  Hacl_Impl_Curve25519_Field64_Vale_fsqr2(dc, ab, tmp2);
  a[0U] = c[0U];
  a[1U] = c[1U];
  a[2U] = c[2U];
  a[3U] = c[3U];
  Hacl_Impl_Curve25519_Field64_Vale_fsub(c, d, c);
  Hacl_Impl_Curve25519_Field64_Vale_fmul1(b, c, (uint64_t)121665U);
  Hacl_Impl_Curve25519_Field64_Vale_fadd(b, b, d);
  Hacl_Impl_Curve25519_Field64_Vale_fmul2(nq, dc, ab, tmp2);
}

static void Hacl_Curve25519_64_montgomery_ladder(uint64_t *out, uint8_t *key, uint64_t *init1)
{
  uint64_t tmp2[16U] = { 0U };
  uint64_t p01_tmp1_swap[33U] = { 0U };
  uint64_t *p0 = p01_tmp1_swap;
  uint64_t *p01 = p01_tmp1_swap;
  uint64_t *p03 = p01;
  uint64_t *p11 = p01 + (uint32_t)8U;
  memcpy(p11, init1, (uint32_t)8U * sizeof init1[0U]);
  uint64_t *x0 = p03;
  uint64_t *z0 = p03 + (uint32_t)4U;
  x0[0U] = (uint64_t)1U;
  x0[1U] = (uint64_t)0U;
  x0[2U] = (uint64_t)0U;
  x0[3U] = (uint64_t)0U;
  z0[0U] = (uint64_t)0U;
  z0[1U] = (uint64_t)0U;
  z0[2U] = (uint64_t)0U;
  z0[3U] = (uint64_t)0U;
  uint64_t *p01_tmp1 = p01_tmp1_swap;
  uint64_t *p01_tmp11 = p01_tmp1_swap;
  uint64_t *nq1 = p01_tmp1_swap;
  uint64_t *nq_p11 = p01_tmp1_swap + (uint32_t)8U;
  uint64_t *swap1 = p01_tmp1_swap + (uint32_t)32U;
  Hacl_Impl_Curve25519_Field64_Vale_cswap2((uint64_t)1U, nq1, nq_p11);
  Hacl_Curve25519_64_point_add_and_double(init1, p01_tmp11, tmp2);
  swap1[0U] = (uint64_t)1U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)251U; i = i + (uint32_t)1U)
  {
    uint64_t *p01_tmp12 = p01_tmp1_swap;
    uint64_t *swap2 = p01_tmp1_swap + (uint32_t)32U;
    uint64_t *nq2 = p01_tmp12;
    uint64_t *nq_p12 = p01_tmp12 + (uint32_t)8U;
    uint64_t
    bit =
      (uint64_t)(key[((uint32_t)253U - i)
      / (uint32_t)8U]
      >> ((uint32_t)253U - i) % (uint32_t)8U
      & (uint8_t)1U);
    uint64_t sw = swap2[0U] ^ bit;
    Hacl_Impl_Curve25519_Field64_Vale_cswap2(sw, nq2, nq_p12);
    Hacl_Curve25519_64_point_add_and_double(init1, p01_tmp12, tmp2);
    swap2[0U] = bit;
  }
  uint64_t sw = swap1[0U];
  Hacl_Impl_Curve25519_Field64_Vale_cswap2(sw, nq1, nq_p11);
  uint64_t *nq10 = p01_tmp1;
  uint64_t *tmp1 = p01_tmp1 + (uint32_t)16U;
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  Hacl_Curve25519_64_point_double(nq10, tmp1, tmp2);
  memcpy(out, p0, (uint32_t)8U * sizeof p0[0U]);
}

static void
Hacl_Curve25519_64_fsquare_times(uint64_t *o, uint64_t *inp, uint64_t *tmp, uint32_t n1)
{
  Hacl_Impl_Curve25519_Field64_Vale_fsqr(o, inp, tmp);
  for (uint32_t i = (uint32_t)0U; i < n1 - (uint32_t)1U; i = i + (uint32_t)1U)
  {
    Hacl_Impl_Curve25519_Field64_Vale_fsqr(o, o, tmp);
  }
}

static void Hacl_Curve25519_64_finv(uint64_t *o, uint64_t *i, uint64_t *tmp)
{
  uint64_t t1[16U] = { 0U };
  uint64_t *a = t1;
  uint64_t *b = t1 + (uint32_t)4U;
  uint64_t *c = t1 + (uint32_t)8U;
  uint64_t *t00 = t1 + (uint32_t)12U;
  uint64_t *tmp1 = tmp;
  Hacl_Curve25519_64_fsquare_times(a, i, tmp1, (uint32_t)1U);
  Hacl_Curve25519_64_fsquare_times(t00, a, tmp1, (uint32_t)2U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, i, tmp);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(a, b, a, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, a, tmp1, (uint32_t)1U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)5U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(c, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, c, tmp1, (uint32_t)20U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)10U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(b, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, b, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(c, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, c, tmp1, (uint32_t)100U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, c, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)50U);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(t00, t00, b, tmp);
  Hacl_Curve25519_64_fsquare_times(t00, t00, tmp1, (uint32_t)5U);
  uint64_t *a0 = t1;
  uint64_t *t0 = t1 + (uint32_t)12U;
  Hacl_Impl_Curve25519_Field64_Vale_fmul(o, t0, a0, tmp);
}

static void Hacl_Curve25519_64_store_felem(uint64_t *b, uint64_t *f)
{
  uint64_t f30 = f[3U];
  uint64_t top_bit0 = f30 >> (uint32_t)63U;
  f[3U] = f30 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry = Hacl_Impl_Curve25519_Field64_Vale_add1(f, f, (uint64_t)19U * top_bit0);
  uint64_t f31 = f[3U];
  uint64_t top_bit = f31 >> (uint32_t)63U;
  f[3U] = f31 & (uint64_t)0x7fffffffffffffffU;
  uint64_t carry0 = Hacl_Impl_Curve25519_Field64_Vale_add1(f, f, (uint64_t)19U * top_bit);
  uint64_t f0 = f[0U];
  uint64_t f1 = f[1U];
  uint64_t f2 = f[2U];
  uint64_t f3 = f[3U];
  uint64_t m0 = FStar_UInt64_gte_mask(f0, (uint64_t)0xffffffffffffffedU);
  uint64_t m1 = FStar_UInt64_eq_mask(f1, (uint64_t)0xffffffffffffffffU);
  uint64_t m2 = FStar_UInt64_eq_mask(f2, (uint64_t)0xffffffffffffffffU);
  uint64_t m3 = FStar_UInt64_eq_mask(f3, (uint64_t)0x7fffffffffffffffU);
  uint64_t mask = ((m0 & m1) & m2) & m3;
  uint64_t f0_ = f0 - (mask & (uint64_t)0xffffffffffffffedU);
  uint64_t f1_ = f1 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f2_ = f2 - (mask & (uint64_t)0xffffffffffffffffU);
  uint64_t f3_ = f3 - (mask & (uint64_t)0x7fffffffffffffffU);
  uint64_t o0 = f0_;
  uint64_t o1 = f1_;
  uint64_t o2 = f2_;
  uint64_t o3 = f3_;
  b[0U] = o0;
  b[1U] = o1;
  b[2U] = o2;
  b[3U] = o3;
}

static void Hacl_Curve25519_64_encode_point(uint8_t *o, uint64_t *i)
{
  uint64_t *x = i;
  uint64_t *z = i + (uint32_t)4U;
  uint64_t tmp[4U] = { 0U };
  uint64_t u64s[4U] = { 0U };
  uint64_t tmp_w[16U] = { 0U };
  Hacl_Curve25519_64_finv(tmp, z, tmp_w);
  Hacl_Impl_Curve25519_Field64_Vale_fmul(tmp, tmp, x, tmp_w);
  Hacl_Curve25519_64_store_felem(u64s, tmp);
  for (uint32_t i0 = (uint32_t)0U; i0 < (uint32_t)4U; i0 = i0 + (uint32_t)1U)
  {
    store64_le(o + i0 * (uint32_t)8U, u64s[i0]);
  }
}

void Hacl_Curve25519_64_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint64_t init1[8U] = { 0U };
  uint64_t tmp[4U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)4U; i = i + (uint32_t)1U)
  {
    uint64_t *os = tmp;
    uint8_t *bj = pub + i * (uint32_t)8U;
    uint64_t u = load64_le(bj);
    uint64_t r = u;
    uint64_t x = r;
    os[i] = x;
  }
  uint64_t tmp3 = tmp[3U];
  tmp[3U] = tmp3 & (uint64_t)0x7fffffffffffffffU;
  uint64_t *x = init1;
  uint64_t *z = init1 + (uint32_t)4U;
  z[0U] = (uint64_t)1U;
  z[1U] = (uint64_t)0U;
  z[2U] = (uint64_t)0U;
  z[3U] = (uint64_t)0U;
  x[0U] = tmp[0U];
  x[1U] = tmp[1U];
  x[2U] = tmp[2U];
  x[3U] = tmp[3U];
  Hacl_Curve25519_64_montgomery_ladder(init1, priv, init1);
  Hacl_Curve25519_64_encode_point(out, init1);
}

void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv)
{
  uint8_t basepoint[32U] = { 0U };
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t *os = basepoint;
    uint8_t x = Hacl_Curve25519_64_g25519[i];
    os[i] = x;
  }
  Hacl_Curve25519_64_scalarmult(pub, priv, basepoint);
}

bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub)
{
  uint8_t zeros1[32U] = { 0U };
  Hacl_Curve25519_64_scalarmult(out, priv, pub);
  uint8_t res = (uint8_t)255U;
  for (uint32_t i = (uint32_t)0U; i < (uint32_t)32U; i = i + (uint32_t)1U)
  {
    uint8_t uu____0 = FStar_UInt8_eq_mask(out[i], zeros1[i]);
    res = uu____0 & res;
  }
  uint8_t z = res;
  bool r = z == (uint8_t)255U;
  return !r;
}

