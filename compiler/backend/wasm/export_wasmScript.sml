open preamble
open base64Theory

val () = new_theory "export_wasm";

val wasm_export_def = Define `
  wasm_export ffi_names heap_space stack_space bytes data = encode_mime data
`

val _ = export_theory ()
