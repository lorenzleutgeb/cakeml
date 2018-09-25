(* NOTE: This theory is based on
 *
 *  WebAssembly Core Specification
 *  W3C First Public Working Draft, 4 September 2018
 *
 * which is available at
 *
 *  https://w3.org/tr/2018/wd-wasm-core-1-20180904
 *
 * At the time of writing (September 2018), the version
 * above is not significantly outdated. To compare
 * against the most current version, see
 *
 *  https://github.com/webassembly/spec
 *
 * The ordering of definitions is meant to mirror the
 * original document. However, some exceptions were
 * made to have all definitions "straight forward".
 * These exceptions are marked with comments.
 *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory arithmeticTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmLang"

(* Type for nonempty lists. *)
val _ = Datatype `nlist = NBASE 'a | NCONS 'a nlist`

val to_list_def = Define `
  (to_list (NBASE a)   = CONS a NIL) /\
  (to_list (NCONS a y) = CONS a (to_list y))`

val to_nlist_def = Define `
  (to_nlist (CONS a NIL)) = NBASE a /\
  (to_nlist (CONS a y))   = NCONS a (to_nlist y)`

val nlist_last_length = store_thm(
  "nlist_last_length",
  ``!isne. (to_list isne) <> []``,
  Cases_on `isne` >> rw[to_list_def]
)

(* 2  Structure *)

(* 2.1.1  Grammar Notation
 * A^n is translated as A list
   TODO: For the vector type below, this means that maximum length is not enforced!
 * A^* is translated as A list
 * A^+ is translated as A nlist
 * A^? is translated as A option
 *)

(* 2.1.3  Vectors *)
(* TODO: Is there a type that better represents a vector? *)
val _ = temp_type_abbrev("vec", ``:'a list``)

(* 2.2.1  Bytes *)
val _ = type_abbrev("byte", ``:8 word``)

(* 2.2.2  Integers *)
(* Only the commonly used ones are named. *)
val _ = type_abbrev("u32", ``:32 word``)
val _ = type_abbrev("s32", ``:32 word``)
val _ = type_abbrev("i32", ``:u32``)
val _ = type_abbrev("u64", ``:64 word``)
val _ = type_abbrev("s64", ``:64 word``)
val _ = type_abbrev("i64", ``:u64``)

(* 2.2.4  Names *)
val _ = temp_type_abbrev("name", ``:(byte list)``)

val string_to_name_def = Define `string_to_name = MAP (\c. n2w_itself (ORD c, (:8)))`
val name_to_string_def = Define `name_to_string = MAP (\c. CHR (w2n c) )`

val ORD_MOD_BOUND = Q.store_thm("ORD_MOD_BOUND",
  `(ORD x) MOD 256n = (ORD x)`,
  rw [stringTheory.ORD_BOUND]
)

val CHR_ORD_MOD_EQ_CHR_ORD = Q.store_thm("CHR_ORD_MOD_EQ_CHR_ORD",
  `CHR ((ORD x) MOD 256n) = CHR (ORD x)`,
  rw [ORD_MOD_BOUND]
)

val string_to_name_to_string = Q.store_thm("string_to_name_to_string",
  `name_to_string (string_to_name s) = s`,
  rw [name_to_string_def,string_to_name_def] >>
  Induct_on `s`
  >- (rw [wordsTheory.n2w_itself_def])
  >- (
    rw [listTheory.MAP_EQ_APPEND] >>
    rw [wordsTheory.n2w_itself_def,CHR_ORD_MOD_EQ_CHR_ORD,stringTheory.CHR_ORD]
  )
)

(* 2.3.1  Value Types *)
(* The spec defines {i,f}{32,64} as atomic types. We separate along "kind"
 * (integer or float) as well as "width" (32bit or 64bit) to have a little
 * more control over parts where the spec resorts to meta language.
 *)
val _ = Datatype `kind  = Ki  | Kf`
val _ = Datatype `width = W32 | W64`

val _ = Datatype `valtype = Tv kind width`

val _ = overload_on("T_i32", ``Tv Ki W32``)
val _ = overload_on("T_i64", ``Tv Ki W64``)
val _ = overload_on("T_f32", ``Tv Kf W32``)
val _ = overload_on("T_f64", ``Tv Kf W64``)

val _ = Define `flip_width W32 = W64 /\ flip_width W64 = W32`
val _ = Define `flip_kind  Ki  = Kf  /\ flip_kind  Kf  = Ki`

val _ = Define `other_kind  (Tv k w) = Tv (flip_kind k)            w `
val _ = Define `other_width (Tv k w) = Tv            k (flip_width w)`

val _ = Define `kindof  (Tv k w) = k`
val _ = Define `widthof (Tv k w) = w`

(* 4.2.1  Values *)
(* Along with their types, we also define values. This enables direct definition
 * of the constant instruction. *)
val _ = Datatype `val = V_i32 word32 | V_i64 word64 | V_f32 word32 | V_f64 word64`

val typeof_def = Define `
  typeof v = case v of
    | V_i32 _ => T_i32
    | V_i64 _ => T_i64
    | V_f32 _ => T_f32
    | V_f64 _ => T_f64`

val val2w_def = Define `
  val2w v = case v of
    | V_i32 w => w2w w
    | V_i64 w => w2w w
    | V_f32 w => w2w w
    | V_f64 w => w2w w`

val w2val_def = Define `
  w2val t = case t of
    | Tv Ki W32 => V_i32 o w2w
    | Tv Ki W64 => V_i64 o w2w
    | Tv Kf W32 => V_f32 o w2w
    | Tv Kf W64 => V_f64 o w2w`

val w2val2w = Q.store_thm("w2val2w",
  `w2val (typeof v) (val2w v) = v`,
  rw [w2val_def, typeof_def, val2w_def] >>
  Cases_on `v` >>
  rw [] >>
  cheat
  (* simp [wordsTheory.w2w_w2w] *)
  (* simp [wordsTheory.WORD_w2w_EXTRACT] *)
  (* simp [wordsTheory.w2w] *)
)

val val2w2val = Q.store_thm("val2w2val",
  `val2w (w2val t w) = w`,
  cheat
)

val zero_def = Define `
  zero t = case t of
    | Tv Ki W32 => V_i32 0w
    | Tv Ki W64 => V_i64 0w
    | Tv Kf W32 => V_f32 0w
    | Tv Kf W64 => V_f64 0w`

val wasm_width_def = Define `wasm_width a = if dimword(a) <= dimword(:32) then W32 else W64`

(* 2.3.1.1  Conventions *)
val bit_width_def = Define `bit_width (Tv k W32) = 32n /\ bit_width (Tv k W64) = 64n`

val _ = Datatype `sz = S8 | S16 | S32`

val bit_width_p_def = Define `bit_width_p S8 = 8n /\ bit_width_p S16 = 16n /\ bit_width_p S32 = 32n`

(* 2.3.2  Result Types *)
(* TODO: This may be a bit too general. Currently,
         wasm allows these lists to be of length <= 1. *)
val _ = type_abbrev("resulttype", ``:(valtype list)``)

(* 2.3.3  Function Types *)
val _ = Datatype `functype = Tf (valtype vec) (valtype vec)`
val _ = set_mapped_fixity {tok = "_>", fixity = Infixr 700, term_name = "Tf"}
val _ = set_mapped_fixity {tok = "⟿", fixity = Infixr 700, term_name = "Tf"}

(* Function used for foreign functions in CakeML. *)
val _ = overload_on("ffi_type", ``Tf [T_i32; T_i32; T_i32; T_i32] []``)

(* 2.3.4  Limits *)
val _ = Datatype `limits = <| min: u32; max: u32 option |>`

(* Auxiliary to denote limits that enfore a specific n. *)
val limits_exact_def = Define `limits_exact n = <| min := n; max := SOME n |>`

(* 2.3.5  Memory Types *)
(* NOTE: min and max are given in units of page size. According to section 4.2.8
 * one page size is defined as 64KiB = 65536B. *)
val _ = overload_on("page_size", ``65536n``)
val _ = temp_type_abbrev("memtype", ``:limits``)

(* 2.3.6  Table Types *)
(* NOTE: We only have one constructor for elemtype, which might seem odd,
 *       but the spec explicitly mentions that there might be more in the
 *       future.
 *)
val _ = Datatype `elemtype = T_anyfunc`
val _ = Datatype `tabletype = T_table limits elemtype`

(* 2.3.7  Global Types *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#global-types%E2%91%A0 *)
val _ = Datatype `mut = T_const | T_var`
val _ = Datatype `globaltype = T_global mut valtype`

val is_var_def = Define `is_var gt = case gt of T_global T_var _ => T | _ => F`

(* 2.3.8  External Types *)
val _ = Datatype `
  externtype =
    | Te_func     functype
    | Te_table   tabletype
    | Te_mem       memtype
    | Te_global globaltype`

(* 2.3.8.1  Conventions *)
val _ = Define `ext_funcs   = FOLDR (\x l. case x of Te_func   y => y::l | _ => l) []`
val _ = Define `ext_tables  = FOLDR (\x l. case x of Te_table  y => y::l | _ => l) []`
val _ = Define `ext_mems    = FOLDR (\x l. case x of Te_mem    y => y::l | _ => l) []`
val _ = Define `ext_globals = FOLDR (\x l. case x of Te_global y => y::l | _ => l) []`

(* 2.4  Instructions *)
val _ = Datatype `sx = S | U`

val _ = Datatype `iunop = Clz | Ctz | Popcnt`

val _ = Datatype `
  ibinop =
    | Add    | And  | Shl
    | Sub    | Or   | Shr sx
    | Mul    | Xor  | Rotl
    | Div sx        | Rotr
    | Rem sx
`

val _ = Datatype `funop = Negf | Absf | Ceilf | Floorf | Truncf | Nearestf | Sqrtf`

val _ = Datatype `fbinop = Addf | Subf | Mulf | Divf | Min | Max | Copysign`

val _ = Datatype `itestop = Eqz`
val _ = Datatype ` irelop = Eq  | Ne  | Lt  sx | Gt  sx | Le  sx | Ge  sx`
val _ = Datatype ` frelop = Eqf | Nef | Ltf    | Gtf    | Lef    | Gef`

(* All conversions grouped. *)
val _ = Datatype `conv =
  | Wrap        (*i32*)    (*i64*)
  | Extend      (*i64*) sx (*i32*)
  | Trunc        width  sx  width
  | Demote      (*f32*)    (*f64*)
  | Promote     (*f64*)    (*f32*)
  | Convert      width  sx  width
  | Reinterpret  valtype (* one side is given, the other is implicit *)`

val _ = Datatype `memarg = <| offset: word32; align: word32 |>`

(* 2.5.1  Indices *)
(* Moved up since instr depends on indices. *)
val _ = temp_type_abbrev(  "typeidx", ``:word32``)
val _ = temp_type_abbrev(  "funcidx", ``:word32``)
val _ = temp_type_abbrev( "tableidx", ``:word32``)
val _ = temp_type_abbrev(   "memidx", ``:word32``)
val _ = temp_type_abbrev("globalidx", ``:word32``)
val _ = temp_type_abbrev( "localidx", ``:word32``)
val _ = temp_type_abbrev( "labelidx", ``:word32``)

val _ = Datatype `
  instr =
(* 2.4.1  Numeric Instructions *)
    | Const val
    | Unop_i   width   iunop
    | Unop_f   width   funop
    | Binop_i  width  ibinop
    | Binop_f  width  fbinop
    | Testop_i width itestop
    | Relop_i  width  irelop
    | Relop_f  width  frelop
    (* NOTE: Conversion is not an actual instruction but groups conversions. *)
    | Conversion conv
(* 2.4.2  Parametric Instructions *)
    | Drop
    | Select
(* 2.4.3  Variable Instructions *)
    | Get_local   localidx
    | Set_local   localidx
    | Tee_local   localidx
    | Get_global globalidx
    | Set_global globalidx
(* 2.4.4  Memory Instructions *)
    (* Load and Store use the full width and are applicable to both floats and integers. *)
    | Load   valtype       memarg
    | Store  valtype       memarg
    (* Loadi and Storei are only applicable to integers and use reduced width through tp. *)
    | Loadi  width   sz sx memarg
    | Storei width   sz    memarg
    | MemorySize
    | MemoryGrow
(* 2.4.5  Control Instructions *)
    | Unreachable
    | Nop
    | Block resulttype (instr list)
    | Loop  resulttype (instr list)
    | If    resulttype (instr list) (instr list)
    | Br    labelidx
    | Br_if labelidx
    | Br_table (labelidx nlist) labelidx
    | Return
    | Call funcidx
    | Call_indirect typeidx`

(* Shortcuts for constants *)

val ci32_def = Define `ci32 = Const o V_i32`
val ci64_def = Define `ci64 = Const o V_i64`

val cf32_def = Define `cf32 = Const o V_f32`
val cf64_def = Define `cf64 = Const o V_f64`

(* 2.4.6  Expressions *)
val _ = Datatype `expr = Expr (instr list)`

(* TODO: Think about whether we actually need a separate Expr type... *)
val expr_to_instrs = Define `expr_to_instrs (Expr instrs) = instrs`

(* 2.5  Modules *)
(* The definition of module is at the end of the section. *)
(* 2.5.1  Indices [moved-up] *)
(* 2.5.2  Types [empty] *)

(* 2.5.3  Functions *)
val _ = Datatype `func = <| type: typeidx; locals: valtype vec; body: expr |>`

(* 2.5.4  Tables *)

(* NOTE:
 * Blog article on table imports:
 *  https://hacks.mozilla.org/2017/07/webassembly-table-imports-what-are-they/
 *
 * Some reasoning behind tables:
 *  https://github.com/WebAssembly/design/issues/898
 *  https://github.com/WebAssembly/design/issues/1117
 *
 * Future features on tables:
 *  https://github.com/WebAssembly/design/blob/master/FutureFeatures.md#more-table-operators-and-types
 *
 * JavaScript API on WebAssembly.Table Objects:
 *  https://www.w3.org/TR/2018/WD-wasm-js-api-1-20180215/#tables
 *  https://github.com/WebAssembly/design/blob/master/JS.md#webassemblytable-objects
*)
val _ = Datatype `table = <| type: tabletype |>`

(* 2.5.5  Memories *)
val _ = Datatype `mem = <| type: memtype |>`

(* 2.5.6  Globals *)
val _ = Datatype `global = <| type: globaltype; init: expr |>`

val global_zero_def = Define `global_zero mut t = <| type := T_global mut t; init := Expr [Const (zero t)] |>`

(* 2.5.7  Element Segments *)
val _ = Datatype `elem = <| table: tableidx; offset: expr; init: funcidx vec |>`

(* 2.5.8  Data Segments *)
val _ = Datatype `data = <| data: memidx; offset: expr; init: byte vec |>`

(* 2.5.9  Start Function *)
val _ = Datatype `start = <| func: funcidx |>`

(* 2.5.10  Exports *)
val _ = Datatype `
  exportdesc =
    | Export_func     funcidx
    | Export_table   tableidx
    | Export_mem       memidx
    | Export_global globalidx`

val _ = Datatype `export = <| name: name; desc: exportdesc |>`

(* 2.5.11  Imports *)
val _ = Datatype `
  importdesc =
    | Import_func      typeidx
    | Import_table   tabletype
    | Import_mem       memtype
    | Import_global globaltype`

val _ = Datatype `import = <| module: name; name: name; desc: importdesc |>`

(* Module name used in CakeML for importing foreing functions. *)
val ffi_module_name_def = Define `ffi_module_name = string_to_name "ffi"`

(* NOTE: The possiblility of multiple tables/mems per module is mentioned at
 *   https://github.com/WebAssembly/design/blob/master/FutureFeatures.md#multiple-tables-and-memories
 *)
val _ = Datatype `module =
  <| types  : functype vec
   ; funcs  : func     vec
   ; tables : table    vec
   ; mems   : mem      vec
   ; globals: global   vec
   ; elem   : elem     vec
   ; data   : data     vec
   ; start  : start    option
   ; imports: import   vec
   ; exports: export   vec
   |>`

val _ = export_theory ()
