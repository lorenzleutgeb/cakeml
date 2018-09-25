open preamble
open wasmLangTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasm_binary"

val word2bytes_def = Define `w2bs w = (MAP n2w (word_to_oct_list w)):(byte list)`

(* 5.2.2  Integers *)

val enc_unsigned_def = Define `
  enc_unsigned n =
    let groups = MAP (\x. n2w x: byte) (n2l (dimword (:7)) n) in
    (MAP (word_or 0x80w) (FRONT groups)) ++ [LAST groups]`

(* Taken from a note in 5.2.2 *)
val enc_unsigned_test_spec = Q.store_thm("enc_unsigned_test_spec",
  `enc_unsigned 3 = [3w]`,
  EVAL_TAC
)

(* Taken from https://en.wikipedia.org/wiki/LEB128#Unsigned_LEB128 *)
val enc_unsigned_test_wikipedia = Q.store_thm("enc_unsigned_test_wikipedia",
  `enc_unsigned 624485 = [229w; 142w; 38w]`,
  EVAL_TAC
)

val enc_signed_def = Define `
  enc_signed i =
    let abs = Num (ABS i) in
    if i >= 0 then enc_unsigned abs else
    (* Variable length expansion with 1s to a length that is a multiple of 7. *)
    let width = (LOG2 abs + 7) DIV 7 * 7 in
    enc_unsigned (2n EXP width - abs)
`

val enc_signed_tests = Q.store_thm("enc_signed_tests",
  `MAP
     enc_signed
     [ ~624485i
     ; ~424091i
     ; ~9019283812387i
     ]
   =
     [ [0x9bw; 0xf1w; 0x59w]
     ; [0xe5w; 0x8ew; 0x66w]
     ; [0xddw; 0x9fw; 0xabw; 0xc6w; 0xc0w; 0xf9w; 0x7dw]
     ]`,
  EVAL_TAC
)

(* TODO: enc_signed and enc_unsigned should work for arbitrarily big nums/ints.
 * However in the spec, most numbers are restricted to be s32/u32, u8 or similar.
 * These functions might take a second parameter that checks whether the given
 * parameter fits this range. E.g. enc_u 32 w should only take words that fit
 * 32bit. *)
val enc_u_def = Define `enc_u = enc_unsigned o w2n`
val enc_s_def = Define `enc_s = enc_signed o w2i`

(* 5.1.3  Vectors *)
val enc_vec_def = Define `enc_vec f v = (enc_u ((n2w (LENGTH v)): word32)) ++ (FLAT (MAP f v)): (byte list)`

(* 5.2.4  Names *)
val enc_name_def = Define `enc_name n = enc_vec (\x.[x]) n`

(* 5.3.1  Value Types *)
val enc_valtype_def = Define `
enc_valtype (Tv Ki W32) = 0x7Fw:byte /\
enc_valtype (Tv Ki W64) = 0x7Ew:byte /\
enc_valtype (Tv Kf W32) = 0x7Dw:byte /\
enc_valtype (Tv Kf W64) = 0x7Cw:byte`

(* 5.3.2  Result Types *)
val enc_resulttype_def = Define `
enc_resulttype [ ] = [0x40w] /\
enc_resulttype [t] = [enc_valtype t]`

val _ = overload_on("enc_blocktype", ``enc_resulttype``)

(* 5.3.3  Function Types *)
val enc_functype_def = Define `
enc_functype (Tf a b) = [0x60w] ++ (enc_vec (\x. [enc_valtype x]) a) ++ (enc_vec (\x. [enc_valtype x]) b)`

(* 5.3.4  Limits *)
val enc_limits_def = Define `
  enc_limits ls = case ls.max of
    | NONE     => [0x00w] ++ (enc_u ls.min)
    | SOME max => [0x01w] ++ (enc_u ls.min) ++ (enc_u max)`

(* 5.3.5  Memory Types *)
val _ = overload_on("enc_memtype", ``enc_limits``)

(* 5.3.6  Table Types *)
val enc_elemtype_def = Define `enc_elemtype T_anyfunc = [0x70w]`
val enc_tabletype_def = Define `enc_tabletype (T_table ls et) = (enc_elemtype et) ++ (enc_limits ls)`

(* 5.3.7  Global Types *)
val enc_mut_def = Define `enc_mut T_const = 0x00w:byte /\ enc_mut T_var = 0x01w:byte`
val enc_globaltype_def = Define `enc_globaltype (T_global m t) = [enc_valtype t; enc_mut m]`

(* 5.5.1  Indices *)
val enc_idx_def = Define `enc_idx (i:word32) = enc_u i`

val enc_memarg_def = Define `enc_memarg ma = (enc_idx ma.align) ++ (enc_idx ma.offset)`

(* 5.4  Instructions *)

val enc_relop_i_def = Define `
  enc_relop_i x = case INDEX_OF x [Eq; Ne; Lt S; Lt U; Gt S; Gt U; Le S; Le U; Ge S; Ge U] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_relop_f_def = Define `
  enc_relop_f x = case INDEX_OF x [Eqf; Nef; Ltf; Gtf; Lef; Gef] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_binop_i_def = Define `
  enc_binop_i x = case INDEX_OF x [Add; Sub; Mul; Div S; Div U; Rem S; Rem U; And; Or; Xor; Shl; Shr S; Shr U; Rotl; Rotr] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_unop_f_def = Define `
  enc_unop_f x = case INDEX_OF x [Absf; Negf; Ceilf; Floorf; Truncf; Nearestf; Sqrtf] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_binop_f_def = Define `
  enc_binop_f x = case INDEX_OF x [Addf; Subf; Mulf; Divf; Min; Max; Copysign] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_conv_def = Define `
  enc_conv x = case INDEX_OF x [Wrap; Trunc W32 S W32; Trunc W32 U W32; Trunc W32 S W64; Trunc W32 U W64; Extend S; Extend U; Trunc W64 S W32; Trunc W64 U W32; Trunc W64 S W64; Trunc W64 U W64; Convert W32 S W32; Convert W32 U W32; Convert W32 S W64; Convert W32 U W64; Demote; Convert W64 S W32; Convert W64 U W32; Convert W64 S W64; Convert W64 U W64; Promote; Reinterpret T_i32; Reinterpret T_i64; Reinterpret T_f32; Reinterpret T_f64] of
    | SOME i => (n2w i: byte)
    | _ => 0w:byte`

val enc_sz_def = Define `
  enc_sz z = case z of
    | S8  => 0w
    | S16 => 1w
    | S32 => 2w`

val enc_sx_def = Define `
  enc_sx x = case x of
    | S => 0w
    | U => 1w`

val enc_instr_def = tDefine "enc_instr" `
  enc_instr i = (case i of
(* 5.4.1  Control Instructions *)
    | Unreachable     => [0x00w]
    | Nop             => [0x01w]
    | Block t is      => [0x02w] ++ (enc_blocktype t) ++ (enc_instrs is) ++ [0x0Bw]
    | Loop t is       => [0x03w] ++ (enc_blocktype t) ++ (enc_instrs is) ++ [0x0Bw]
    | If t i1s []     => [0x04w] ++ (enc_blocktype t) ++ (enc_instrs i1s) ++ [0x0Bw]
    | If t i1s i2s    => [0x04w] ++ (enc_blocktype t) ++ (enc_instrs i1s) ++ [0x05w] ++ (enc_instrs i2s) ++ [0x0Bw]
    | Br l            => [0x0Cw] ++ (enc_idx l)
    | Br_if l         => [0x0Dw] ++ (enc_idx l)
    | Br_table ls ln  => [0x0Ew] ++ (enc_vec enc_idx (to_list ls)) ++ (enc_idx ln)
    | Return          => [0x0Fw]
    | Call x          => [0x10w] ++ (enc_idx x)
    | Call_indirect x => [0x11w] ++ (enc_idx x) ++ [0x00w]
(* 5.4.2  Parametric Instructions *)
    | Drop   => [0x1Aw]
    | Select => [0x1Bw]
(* 5.4.3  Variable Instructions *)
    | Get_local  x => [0x20w] ++ (enc_idx x)
    | Set_local  x => [0x21w] ++ (enc_idx x)
    | Tee_local  x => [0x22w] ++ (enc_idx x)
    | Get_global x => [0x23w] ++ (enc_idx x)
    | Set_global x => [0x24w] ++ (enc_idx x)
(* 5.4.4  Memory Instructions *)
    | Load  t       ma => [enc_valtype t - 0x57w] ++ (enc_memarg ma)
    | Loadi W32 z x ma => [word_add 0x2Cw (word_add (word_mul 2w (enc_sz z)) (enc_sx x))] ++ (enc_memarg ma)
    | Loadi W64 z x ma => [word_add 0x30w (word_add (word_mul 2w (enc_sz z)) (enc_sx x))] ++ (enc_memarg ma)
    | Store  t      ma => [enc_valtype t - 0x49w] ++ (enc_memarg ma)
    | Storei W32 z  ma => [word_add 0x3Aw (enc_sz z)]
    | Storei W64 z  ma => [word_add 0x3Cw (enc_sz z)]
    | MemorySize       => [0x3Fw; 0x00w]
    | MemoryGrow       => [0x40w; 0x00w]
(* 5.4.5  Numeric Instructions *)
    | Const (V_i32 v) => [0x41w] ++ (enc_s v)
    | Const (V_i64 v) => [0x42w] ++ (enc_s v)
    | Const (V_f32 v) => [0x43w] ++ (w2bs  v)
    | Const (V_f64 v) => [0x44w] ++ (w2bs  v)
    | Testop_i W32 Eqz => [0x45w]
    | Relop_i W32 r => [word_add 0x46w (enc_relop_i r)]
    | Testop_i W64 Eqz => [0x50w]
    | Relop_i W64 r => [word_add 0x51w (enc_relop_i r)]
    | Relop_f W32 r => [word_add 0x5Bw (enc_relop_f r)]
    | Relop_f W64 r => [word_add 0x61w (enc_relop_f r)]
    | Unop_i W32 Clz    => [0x67w]
    | Unop_i W32 Ctz    => [0x68w]
    | Unop_i W32 Popcnt => [0x69w]
    | Binop_i W32 r => [word_add 0x6Aw (enc_binop_i r)]
    | Unop_i W64 Clz    => [0x79w]
    | Unop_i W64 Ctz    => [0x7Aw]
    | Unop_i W64 Popcnt => [0x7Bw]
    | Binop_i W64 r => [word_add 0x7Cw (enc_binop_i r)]
    | Unop_f  W32 r => [word_add 0x8Bw (enc_unop_f r)]
    | Binop_f W32 r => [word_add 0x92w (enc_binop_f r)]
    | Unop_f  W64 r => [word_add 0x99w (enc_unop_f r)]
    | Binop_f W64 r => [word_add 0xA0w (enc_binop_f r)]
    | Conversion c => [word_add 0xA7w (enc_conv c)]
  ) /\
  enc_instrs is = (FLAT (MAP enc_instr is))`
(
  WF_REL_TAC `measure (\s. sum_CASE s (instr_size) (instr1_size))` >>
  rw [listTheory.list_size_def, wasmLangTheory.instr_size_def, wasmLangTheory.valtype_size_def, pairTheory.LEX_DEF, sumTheory.OUTL, sumTheory.OUTR] >>
  cheat
)

(* 5.4.6  Expressions *)
val enc_expr_def = Define `enc_expr (Expr is) = (enc_instrs is) ++ [0xBw]`

(* 5.5.2  Sections *)
val sec_def = Define `sec id bs = [(n2w id):byte] ++ (enc_unsigned (LENGTH bs)) ++ bs`

val vecsec_def = Define `vecsec id f [] = [] /\ vecsec id f v = sec id (enc_vec f v)`

(* 5.5.4  Type Section *)
val typesec_def = Define `
typesec [] = [] /\
typesec ts = [0x01w] ++ (enc_vec enc_functype ts)`

(* 5.5.5  Import Section *)
val enc_importdesc_def = Define `
  enc_importdesc id = case id of
    | Import_func   x  => [0x00w] ++ (enc_idx x)
    | Import_table  tt => [0x01w] ++ (enc_tabletype tt)
    | Import_mem    mt => [0x02w] ++ (enc_memtype mt)
    | Import_global gt => [0x03w] ++ (enc_globaltype gt)`

val enc_import_def = Define `enc_import i = (enc_name i.module) ++ (enc_name i.name) ++ (enc_importdesc i.desc)`

val importsec_def = Define `importsec = vecsec 2 enc_import`

(* 5.5.6  Function Section *)
val funcsec_def = Define `funcsec = vecsec 3 enc_idx`

(* 5.5.7  Table Section *)
val enc_table_def = Define `enc_table t = (enc_tabletype t.type)`
val tablesec_def = Define `tablesec = vecsec 4 enc_table`

(* 5.5.8  Memory Section *)
val enc_mem_def = Define `enc_mem m = enc_memtype m.type`
val memsec_def = Define `memsec = vecsec 5 (\m. enc_memtype m.type)`

(* 5.5.9  Global Section *)
val enc_global = Define `enc_global g = (enc_globaltype g.type) ++ (enc_expr g.init)`
val globalsec_def = Define `globalsec = vecsec 6 enc_global`

(* 5.5.10  Export Section *)
val enc_exportdesc_def = Define `
  enc_exportdesc ed = case ed of
    | Export_func   x => [0x00w] ++ (enc_idx x)
    | Export_table  x => [0x01w] ++ (enc_idx x)
    | Export_mem    x => [0x02w] ++ (enc_idx x)
    | Export_global x => [0x03w] ++ (enc_idx x)`

val enc_export_def = Define `enc_export e = (enc_name e.name) ++ (enc_exportdesc e.desc)`
val exportsec_def = Define `exportsec = vecsec 7 enc_export`

(* 5.5.11  Start Section *)
val startsec_def = Define `
startsec NONE = [] /\
startsec (SOME x) = sec 8 (enc_idx x.func)`

(* 5.5.12  Element Section *)
val enc_elem_def = Define `enc_elem e = (enc_idx e.table) ++ (enc_expr e.offset) ++ (enc_vec enc_idx e.init)`
val elemsec_def = Define `elemsec = vecsec 9 enc_elem`

(* 5.5.13  Code Section *)

(* TODO: This is horrible... *)
val LIST_COUNT_DEF = Define `
LIST_COUNT [] = [] /\
LIST_COUNT l = REVERSE (FOLDL (\acc curr. let ((prev, count), t) = ((HD acc), (TL acc)) in if prev = curr then (prev, count + 1n)::t else (curr, 1n)::acc) [(HD l, 1n)] (TL l))`

val enc_locals = Define `enc_locals l = (enc_vec (\ (t, n). (enc_unsigned n) ++ [(enc_valtype t)]) (LIST_COUNT l))`

val enc_func_def = Define `enc_func (locals, body) = (enc_locals locals) ++ (enc_expr body)`

(* TODO: Check for length of f. If it is bigger than 2^32 then we have a problem. *)
val enc_code_def = Define `enc_code c = let f = enc_func c in (enc_unsigned (LENGTH f)) ++ f`

val codesec_def = Define `codesec = vecsec 10 enc_code`

(* 5.5.14  Data Section *)
val enc_data_def = Define `enc_data d = (enc_idx d.data) ++ (enc_expr d.offset) ++ (enc_vec (\x.[x]) d.init)`

val datasec_def = Define `datasec = vecsec 11 enc_data`

(* 5.5.15  Modules *)
val _ = overload_on("magic",   ``[0x00w; 0x61w; 0x73w; 0x6Dw]``)
val _ = overload_on("version", ``[0x01w; 0x00w; 0x00w; 0x00w]``)

val enc_module_def = Define `
enc_module m =
  magic ++
  version ++
  (typesec   m.types) ++
  (importsec m.imports) ++
  (funcsec   (MAP (\x. x.type) m.funcs)) ++
  (tablesec  m.tables) ++
  (memsec    m.mems) ++
  (globalsec m.globals) ++
  (exportsec m.exports) ++
  (startsec  m.start) ++
  (elemsec   m.elem) ++
  (codesec   (MAP (\x. (x.locals, x.body)) m.funcs)) ++
  (datasec   m.data)`

val _ = export_theory ()
