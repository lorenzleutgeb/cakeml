(* NOTE: Please consult README.md *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmLang"

val _ = Datatype `ne_list = Base 'a | Conz 'a ne_list`

val to_list_def = Define `
  (to_list (Base a) = [a]) /\
  (to_list (Conz a y) = (a :: (to_list y)))`

val ne_list_last_length = store_thm(
  "ne_list_last_length",
  ``!(isne: 'a ne_list). (to_list isne) <> []``,
  Cases_on `isne` >> rw[to_list_def]
);

(* 2  Structure *)

(* 2.1.1  Grammar Notation
 * A^n is translated as A list
   TODO: For the vector type below, this means that maximum length is not enforced!
 * A^* is translated as A list
 * A^+ is translated as A list
   TODO: For some occurrence below, this means that minimum length is not enforced!
 * A^? is translated as A option
 *)

(* 2.1.3  Vectors *)
(* TODO: Is there a type that better represents a vector? *)
val _ = type_abbrev("vec", ``:'a list``)

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

(* 2.2.3  Floating-Point *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#floating-point%E2%91%A0 *)
val _ = type_abbrev("f32", ``:( 8, 23) float``)
val _ = type_abbrev("f64", ``:(11, 52) float``)

(* 2.2.4  Names *)
(* TODO: Find a better representation for codepoints. *)
val _ = type_abbrev("codepoint", ``:num``)
val _ = type_abbrev("name", ``:(codepoint list)``)

(* 2.3.1  Value Types *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#value-types%E2%91%A0 *)
val _ = Datatype `valtype = T_i32 | T_i64 | T_f32 | T_f64`

(* 2.3.1.1  Conventions *)
val bit_width_def = Define
  `bit_width t = case t of T_i32 => 32n
                         | T_i64 => 64n
                         | T_f32 => 32n
                         | T_f64 => 64n`

val _ = Datatype `tp = Tp_i8 | Tp_i16 | Tp_i32`

val bit_width_p_def = Define `
  bit_width_p Tp_i8 = 8n /\ bit_width_p Tp_i16 = 16n /\ bit_width_p Tp_i32 = 32n`

val is_int_t_def = Define `
  is_int_t t <=> t = T_i32 \/ t = T_i64`

val is_float_t_def = Define `
  is_float_t t <=> t = T_f32 \/ t = T_f64`

val int_float_disjoint = store_thm(
 "int_float_disjoint",
  ``!t. is_int_t t <> is_float_t t``,
  Cases_on `t` >> rw[is_int_t_def,is_float_t_def]
)

(* 2.3.2  Result Types *)
(* TODO: This may be a bit too general. Currently,
         wasm allows these lists to be of length <= 1. *)
val _ = type_abbrev("resulttype", ``:(valtype list)``)

(* 2.3.3  Function Types *)
val _ = Datatype `functype = Tf (valtype vec) (valtype vec)`
val _ = set_mapped_fixity {tok = "_>", fixity = Infixr 700, term_name = "Tf"}
val _ = set_mapped_fixity {tok = "⟿", fixity = Infixr 700, term_name = "Tf"}

(* 2.3.4  Limits *)
val _ = Datatype `limits = <| min: u32; max: u32 option |>`

(* 2.3.5  Memory Types *)
val _ = type_abbrev("memtype", ``:limits``)

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
val _ = Define `ext_funcs = FOLDR (\x l. case x of Te_func y => y::l | _ => l) []`
val _ = Define `ext_tables = FOLDR (\x l. case x of Te_table y => y::l | _ => l) []`
val _ = Define `ext_mems = FOLDR (\x l. case x of Te_mem y => y::l | _ => l) []`
val _ = Define `ext_globals = FOLDR (\x l. case x of Te_global y => y::l | _ => l) []`

(* 2.4  Instructions *)
val _ = Datatype `sx = S | U`

val _ = Datatype `iunop = Clz | Ctz | Popcnt`

val _ = Datatype `
  ibinop =
    | Add
    | Sub
    | Mul
    | Div sx
    | Rem sx
    | And
    | Or
    | Not
    | Shl
    | Shr sx
    | Rotl
    | Rotr`

val _ = Datatype `funop = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt`

val _ = Datatype `fbinop = Addf | Subf | Mulf | Divf | Min | Max | Copysign`

val _ = Datatype `itestop = Eqz`

val _ = Datatype `irelop = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx`

val _ = Datatype `frelop = Eqf | Nef | Ltf | Gtf | Lef | Gef`

val _ = Datatype `cvtop = Convert | Reinterpret`

val _ = Datatype `memarg = <| offset: word32; align: word32 |>`

(* 2.5.1  Indices *)
(* Moved up since instr depends on indices. *)
val _ = type_abbrev(  "typeidx", ``:word32``)
val _ = type_abbrev(  "funcidx", ``:word32``)
val _ = type_abbrev( "tableidx", ``:word32``)
val _ = type_abbrev(   "memidx", ``:word32``)
val _ = type_abbrev("globalidx", ``:word32``)
val _ = type_abbrev( "localidx", ``:word32``)
val _ = type_abbrev( "labelidx", ``:word32``)

(* 4.2.1  Values *)
(* Moved up since frame depends on val. *)
val _ = Datatype `val = V_i32 i32 | V_i64 i64 | V_f32 f32 | V_f64 f64`

val typeof_def = Define `
(! x . typeof (V_i32 x) = T_i32) /\
(! x . typeof (V_i64 x) = T_i64) /\
(! x . typeof (V_f32 x) = T_f32) /\
(! x . typeof (V_f64 x) = T_f64)`

(* 4.2.4  Addresses *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#addresses%E2%91%A0 *)
(* Moved up since externval needs addrs. *)
val _ = type_abbrev(      "addr", ``:num``)
val _ = type_abbrev(  "funcaddr", ``:addr``)
val _ = type_abbrev( "tableaddr", ``:addr``)
val _ = type_abbrev(   "memaddr", ``:addr``)
val _ = type_abbrev("globaladdr", ``:addr``)

(* 4.2.11  External Values *)
(* Moved up since exportinst needs externval. *)
val _ = Datatype `
  externval =
    | Func     funcaddr
    | Table   tableaddr
    | Mem       memaddr
    | Global globaladdr`

(* TODO: 4.2.11.1  Conventions *)

(* 4.2.10  Export Instances *)
(* Moved up since moduleinst needs exportinst. *)
val _ = Datatype `exportinst = <| name: name; value: externval |>`

(* 4.2.5  Module Instances *)
(* Moved up since funcinst needs moduleinst. *)
val _ = Datatype `moduleinst =
  <| types      :   functype list
   ; funcaddrs  :   funcaddr list
   ; tableaddrs :  tableaddr list
   ; memaddrs   :    memaddr list
   ; globaladdrs: globaladdr list
   ; exports    : exportinst list
   |>`

(* 4.2.12.3  Frames *)
(* Moved up since instr depends on frame. *)
val _ = Datatype `frame = <| locals: val list; module: moduleinst |>`

val _ = Datatype `
  instr =
(* 2.4.1  Numeric Instructions *)
    | Const val
    | Unop_i   valtype   iunop
    | Unop_f   valtype   funop
    | Binop_i  valtype  ibinop
    | Binop_f  valtype  fbinop
    | Testop_i valtype itestop
    | Relop_i  valtype  irelop
    | Relop_f  valtype  frelop
    | Cvtop    valtype   cvtop valtype (sx option)
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
    | Load valtype  ((tp # sx) option) memarg
    | Store valtype ( tp       option) memarg
    | Current_memory
    | Grow_memory
(* 2.4.5  Control Instructions *)
    | Unreachable
    | Nop
    | Block resulttype (instr list)
    | Loop  resulttype (instr list)
    | If    resulttype (instr list) (instr list)
    | Br    labelidx
    | Br_if labelidx
    (* TODO: labelidx vec should be nonempty! *)
    | Br_table (labelidx vec) labelidx
    | Return
    | Call funcidx
    | Call_indirect typeidx
(* 4.2.13  Administrative Instructions *)
    | Trap
    | Invoke funcaddr
    | Init_elem tableaddr u32 (funcidx list)
    | Init_data memaddr u32 (byte list)
    | Label num (instr list) (instr list)
    | Frame num frame (instr list)`

(* To check whether an instr encodes a val. *)
val is_val_def = Define `is_val (Const v) = T`

(* 2.4.6  Expressions *)
val _ = Datatype `expr = Expr (instr list)`

(* 2.5  Modules *)
(* The definition of module is at the end of the section. *)
(* 2.5.1  Indices [moved-up] *)
(* 2.5.2  Types [empty] *)

(* 2.5.3  Functions *)
val _ = Datatype `func = <| type: typeidx; locals: valtype vec; body: expr |>`

(* 2.5.4  Tables *)
val _ = Datatype `table = <| type: tabletype |>`

(* 2.5.5  Memories *)
val _ = Datatype `mem = <| type: memtype |>`

(* 2.5.6  Globals *)
val _ = Datatype `global = <| type: globaltype; init: expr |>`

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
