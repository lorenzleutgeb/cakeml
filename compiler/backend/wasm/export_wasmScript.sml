open preamble
open base64Theory
open mlstringTheory

val () = new_theory "export_wasm";

val wasm_export_def = Define `
  wasm_export ffi_names heap_space stack_space bytes (datax:(64 word) list) =
    (List [strlit (encode_mime bytes)]: mlstring app_list)
`

val _ = export_theory ()
