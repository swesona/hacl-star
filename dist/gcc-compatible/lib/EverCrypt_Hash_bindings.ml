open Ctypes
module Bindings(F:Cstubs.FOREIGN) =
  struct
    open F
    module Hacl_Spec_applied = (Hacl_Spec_bindings.Bindings)(Hacl_Spec_stubs)
    open Hacl_Spec_applied
    type everCrypt_Hash_alg = spec_Hash_Definitions_hash_alg
    let everCrypt_Hash_alg =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_Hash_alg" 
    let constant everCrypt_Hash_string_of_alg =
      foreign "EverCrypt_Hash_string_of_alg"
        (spec_Hash_Definitions_hash_alg @-> (returning string))
      
    type everCrypt_Hash_broken_alg = spec_Hash_Definitions_hash_alg
    let everCrypt_Hash_broken_alg =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_Hash_broken_alg" 
    type everCrypt_Hash_alg13 = spec_Hash_Definitions_hash_alg
    let everCrypt_Hash_alg13 =
      typedef spec_Hash_Definitions_hash_alg "EverCrypt_Hash_alg13" 
    type everCrypt_Hash_state_s_tags = Unsigned.UInt8.t
    let everCrypt_Hash_state_s_tags =
      typedef uint8_t "EverCrypt_Hash_state_s_tags" 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_MD5_s =
      Unsigned.UInt8.of_int 0 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA1_s =
      Unsigned.UInt8.of_int 1 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_224_s =
      Unsigned.UInt8.of_int 2 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_256_s =
      Unsigned.UInt8.of_int 3 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_384_s =
      Unsigned.UInt8.of_int 4 
    let everCrypt_Hash_state_s_tags_EverCrypt_Hash_SHA2_512_s =
      Unsigned.UInt8.of_int 5 
    type everCrypt_Hash_state_s = [ `everCrypt_Hash_state_s ] structure
    let (everCrypt_Hash_state_s : [ `everCrypt_Hash_state_s ] structure typ)
      = structure "EverCrypt_Hash_state_s_s" 
    let everCrypt_Hash_state_s_tag =
      field everCrypt_Hash_state_s "tag" everCrypt_Hash_state_s_tags 
    type everCrypt_Hash_state_s_val = [ `anonymous ] union
    let (everCrypt_Hash_state_s_val : [ `anonymous ] union typ) = union "" 
    let everCrypt_Hash_state_s_val_case_MD5_s =
      field everCrypt_Hash_state_s_val "case_MD5_s" (ptr uint32_t) 
    let everCrypt_Hash_state_s_val_case_SHA1_s =
      field everCrypt_Hash_state_s_val "case_SHA1_s" (ptr uint32_t) 
    let everCrypt_Hash_state_s_val_case_SHA2_224_s =
      field everCrypt_Hash_state_s_val "case_SHA2_224_s" (ptr uint32_t) 
    let everCrypt_Hash_state_s_val_case_SHA2_256_s =
      field everCrypt_Hash_state_s_val "case_SHA2_256_s" (ptr uint32_t) 
    let everCrypt_Hash_state_s_val_case_SHA2_384_s =
      field everCrypt_Hash_state_s_val "case_SHA2_384_s" (ptr uint64_t) 
    let everCrypt_Hash_state_s_val_case_SHA2_512_s =
      field everCrypt_Hash_state_s_val "case_SHA2_512_s" (ptr uint64_t) 
    let _ = seal everCrypt_Hash_state_s_val 
    let everCrypt_Hash_state_s_u =
      field everCrypt_Hash_state_s "" everCrypt_Hash_state_s_val 
    let _ = seal everCrypt_Hash_state_s 
    let everCrypt_Hash_alg_of_state =
      foreign "EverCrypt_Hash_alg_of_state"
        ((ptr everCrypt_Hash_state_s) @->
           (returning spec_Hash_Definitions_hash_alg))
      
    let everCrypt_Hash_create_in =
      foreign "EverCrypt_Hash_create_in"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_Hash_state_s)))
      
    let everCrypt_Hash_create =
      foreign "EverCrypt_Hash_create"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_Hash_state_s)))
      
    let everCrypt_Hash_init =
      foreign "EverCrypt_Hash_init"
        ((ptr everCrypt_Hash_state_s) @-> (returning void))
      
    let everCrypt_Hash_update_multi_256 =
      foreign "EverCrypt_Hash_update_multi_256"
        ((ptr uint32_t) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let everCrypt_Hash_update =
      foreign "EverCrypt_Hash_update"
        ((ptr everCrypt_Hash_state_s) @->
           ((ptr uint8_t) @-> (returning void)))
      
    let everCrypt_Hash_update_multi =
      foreign "EverCrypt_Hash_update_multi"
        ((ptr everCrypt_Hash_state_s) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let everCrypt_Hash_update_last_256 =
      foreign "EverCrypt_Hash_update_last_256"
        ((ptr uint32_t) @->
           (uint64_t @-> ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    let everCrypt_Hash_update_last =
      foreign "EverCrypt_Hash_update_last"
        ((ptr everCrypt_Hash_state_s) @->
           ((ptr uint8_t) @-> (uint64_t @-> (returning void))))
      
    let everCrypt_Hash_finish =
      foreign "EverCrypt_Hash_finish"
        ((ptr everCrypt_Hash_state_s) @->
           ((ptr uint8_t) @-> (returning void)))
      
    let everCrypt_Hash_free =
      foreign "EverCrypt_Hash_free"
        ((ptr everCrypt_Hash_state_s) @-> (returning void))
      
    let everCrypt_Hash_copy =
      foreign "EverCrypt_Hash_copy"
        ((ptr everCrypt_Hash_state_s) @->
           ((ptr everCrypt_Hash_state_s) @-> (returning void)))
      
    let everCrypt_Hash_hash_256 =
      foreign "EverCrypt_Hash_hash_256"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let everCrypt_Hash_hash_224 =
      foreign "EverCrypt_Hash_hash_224"
        ((ptr uint8_t) @->
           (uint32_t @-> ((ptr uint8_t) @-> (returning void))))
      
    let everCrypt_Hash_hash =
      foreign "EverCrypt_Hash_hash"
        (spec_Hash_Definitions_hash_alg @->
           ((ptr uint8_t) @->
              ((ptr uint8_t) @-> (uint32_t @-> (returning void)))))
      
    type everCrypt_Hash_Incremental_state_s =
      [ `everCrypt_Hash_Incremental_state_s ] structure
    let (everCrypt_Hash_Incremental_state_s :
      [ `everCrypt_Hash_Incremental_state_s ] structure typ) =
      structure "EverCrypt_Hash_Incremental_state_s_s" 
    let everCrypt_Hash_Incremental_state_s_hash_state =
      field everCrypt_Hash_Incremental_state_s "hash_state"
        (ptr everCrypt_Hash_state_s)
      
    let everCrypt_Hash_Incremental_state_s_buf =
      field everCrypt_Hash_Incremental_state_s "buf" (ptr uint8_t) 
    let everCrypt_Hash_Incremental_state_s_total_len =
      field everCrypt_Hash_Incremental_state_s "total_len" uint64_t 
    let _ = seal everCrypt_Hash_Incremental_state_s 
    let everCrypt_Hash_Incremental_alg_of_state =
      foreign "EverCrypt_Hash_Incremental_alg_of_state"
        ((ptr everCrypt_Hash_Incremental_state_s) @->
           (returning spec_Hash_Definitions_hash_alg))
      
    let everCrypt_Hash_Incremental_create_in =
      foreign "EverCrypt_Hash_Incremental_create_in"
        (spec_Hash_Definitions_hash_alg @->
           (returning (ptr everCrypt_Hash_Incremental_state_s)))
      
    let everCrypt_Hash_Incremental_init =
      foreign "EverCrypt_Hash_Incremental_init"
        ((ptr everCrypt_Hash_Incremental_state_s) @-> (returning void))
      
    let everCrypt_Hash_Incremental_update =
      foreign "EverCrypt_Hash_Incremental_update"
        ((ptr everCrypt_Hash_Incremental_state_s) @->
           ((ptr uint8_t) @-> (uint32_t @-> (returning void))))
      
    let everCrypt_Hash_Incremental_finish =
      foreign "EverCrypt_Hash_Incremental_finish"
        ((ptr everCrypt_Hash_Incremental_state_s) @->
           ((ptr uint8_t) @-> (returning void)))
      
    let everCrypt_Hash_Incremental_free =
      foreign "EverCrypt_Hash_Incremental_free"
        ((ptr everCrypt_Hash_Incremental_state_s) @-> (returning void))
      
  end