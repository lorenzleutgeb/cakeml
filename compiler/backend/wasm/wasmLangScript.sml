(* NOTE: Please consult README.md *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmLang";

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

val bit_width_def = Define
  `bit_width t = case t of T_i32 => 32n
                         | T_i64 => 64n
                         | T_f32 => 32n
                         | T_f64 => 64n`

val _ = Datatype `tp = Tp_i8 | Tp_i16 | Tp_i32`

val bit_width_p_def = Define
  `bit_width_p t = case t of Tp_i8  =>  8n
                           | Tp_i16 => 16n
                           | Tp_i32 => 32n`

val is_int_t_def = Define
  `is_int_t t = case t of T_i32 => T
                        | T_i64 => T
                        | T_f32 => F
                        | T_f64 => F`

val is_float_t_def = Define
  `is_float_t t = case t of T_i32 => F
                          | T_i64 => F
                          | T_f32 => T
                          | T_f64 => T`

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

val is_var_def = Define
`is_var gt = case gt of T_global T_var _ => T | _ => F`

(* 2.3.8  External Types *)
val _ = Datatype `externtype =
        Te_func functype
      | Te_table tabletype
      | Te_mem memtype
      | Te_global globaltype`

(* 2.4  Instructions *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#numeric-instructions%E2%91%A0 *)
val _ = Datatype
  `sx = S | U`

val _ = Datatype
  `iunop = Clz | Ctz | Popcnt`

val _ = Datatype
  `ibinop = Add | Sub | Mul | Div sx | Rem sx | And | Or | Not | Shl | Shr sx | Rotl | Rotr`

val _ = Datatype
  `funop = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt`

val _ = Datatype
  `fbinop = Addf | Subf | Mulf | Divf | Min | Max | Copysign`

val _ = Datatype
  `itestop = Eqz`

val _ = Datatype
  `irelop = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx`

val _ = Datatype
  `frelop = Eqf | Nef | Ltf | Gtf | Lef | Gef`

val _ = Datatype
  `cvtop = Convert | Reinterpret`

val _ = Datatype `memarg = <| offset: word32; align: word32 |>`

(* 2.5.1  Indices *)
(* Moved up since instr depends on indices. *)
val _ = type_abbrev("typeidx", ``:word32``)
val _ = type_abbrev("funcidx", ``:word32``)
val _ = type_abbrev("tableidx", ``:word32``)
val _ = type_abbrev("memidx", ``:word32``)
val _ = type_abbrev("globalidx", ``:word32``)
val _ = type_abbrev("localidx", ``:word32``)
val _ = type_abbrev("labelidx", ``:word32``)

(* 4.2.1  Values *)
(* Moved up since frame depends on v. *)
val _ = Datatype `val = ConstInt32 i32 | ConstInt64 i64 | ConstFloat32 f32 | ConstFloat64 f64`

(* 4.2.4  Addresses *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#addresses%E2%91%A0 *)
(* Moved up since externval needs addrs. *)
val _ = type_abbrev("addr", ``:num``)
val _ = type_abbrev("funcaddr", ``:addr``)
val _ = type_abbrev("tableaddr", ``:addr``)
val _ = type_abbrev("memaddr", ``:addr``)
val _ = type_abbrev("globaladdr", ``:addr``)

(* 4.2.11  External Values *)
(* Moved up since exportinst needs externval. *)
val _ = Datatype `externval = Func funcaddr | Table tableaddr | Mem memaddr | Global globaladdr`

(* 4.2.10  Export Instances *)
(* Moved up since moduleinst needs exportinst. *)
val _ = Datatype `exportinst = <| name: name; value: externval |>`

(* 4.2.5  Module Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#module-instances%E2%91%A0 *)
(* Moved up since funcinst needs moduleinst. *)
val _ = Datatype `moduleinst = <|
  types:       functype   list;
  funcaddrs:   funcaddr   list;
  tableaddrs:  tableaddr  list;
  memaddrs:    memaddr    list;
  globaladdrs: globaladdr list;
  exports:     exportinst list
|>`

(* 4.2.12.3  Frames *)
(* Moved up since instr depends on frame. *)
val _ = Datatype `frame = <| locals: val list; module: moduleinst |>`

val _ = Datatype `instr =
(* 2.4.1  Numeric Instructions *)
    Const val
  | Unop_i valtype iunop
  | Unop_f valtype funop
  | Binop_i valtype ibinop
  | Binop_f valtype fbinop
  | Testop_i valtype itestop
  | Relop_i valtype irelop
  | Relop_f valtype frelop
  | Cvtop valtype cvtop valtype (sx option)

(* 2.4.2  Parametric Instructions *)
  | Drop
  | Select

(* 2.4.3  Variable Instructions *)
  | Get_local localidx
  | Set_local localidx
  | Tee_local localidx
  | Get_global globalidx
  | Set_global globalidx

(* 2.4.4  Memory Instructions *)
  | Load valtype ((tp # sx) option) memarg
  | Store valtype (tp option) memarg
  | Current_memory
  | Grow_memory

(* 2.4.5  Control Instructions *)
  | Unreachable
  | Nop
  | Block resulttype (instr list)
  | Loop resulttype (instr list)
  | If resulttype (instr list) (instr list)
  | Br labelidx
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

(* 2.4.1.1  Conventions
val _ = Datatype `unop = iunop + funop`
val _ = Datatype `binop = ibinop + fbinop`
val _ = Datatype `relop = irelop + frelop`
 TODO: cvtop *)

(* NOTE: ctz = count trailing zeros, clz = count leading zeros, popcnt = count 1s *)
val _ = Define
  `app_unop_i iop c =
     (case iop of
     Ctz => 0w
   | Clz => 0w
   | Popcnt => 0w)`

(* NOTE: flags are ignored, as hinted in
 *       https://webassembly.github.io/spec/core/exec/numerics.html#floating-point-operations
 *)
val _ = Define
  `app_unop_f fop c =
                  (case fop of
                    Neg => float_negate c
                  | Abs => float_abs c
                  | Ceil => round roundTowardPositive (float_to_real c)
                  | Floor => round roundTowardNegative (float_to_real c)
                  | Trunc => round roundTowardZero (float_to_real c)
                  | Nearest => round roundTiesToEven (float_to_real c)
                  | Sqrt => SND (float_sqrt roundTiesToEven c))`

val _ = Define
  `app_binop_i iop c1 c2 = (case iop of
                              Add => word_add c1 c2
                            | Sub => word_sub c1 c2
                            | Mul => word_mul c1 c2
                            | Div U => word_div c1 c2
                            | Div S => word_sdiv c1 c2
                            | Rem U => word_mod c1 c2
                            | Rem S => word_smod c1 c2
                            | And => word_and c1 c2
                            | Or => word_or c1 c2
                            | Xor => word_xor c1 c2
                            | Shl => word_lsl c1 (w2n c2)
                            | Shr U => word_lsr c1 (w2n c2)
                            | Shr S => word_asr c1 (w2n c2)
                            | Rotl => word_rol c1 (w2n c2)
                            | Rotr => word_ror c1 (w2n c2))`

val _ = Define
  `app_binop_f fop c1 c2 = (case fop of
                              Addf => SOME (SND (float_add roundTiesToEven c1 c2))
                            | Subf => SOME (SND (float_sub roundTiesToEven c1 c2))
                            | Mulf => SOME (SND (float_mul roundTiesToEven c1 c2))
                            | Divf => SOME (SND (float_div roundTiesToEven c1 c2))
                            | Min => SOME (if float_greater_equal c1 c2 then c2 else c1)
                            | Max => SOME (if float_greater_equal c1 c2 then c1 else c2)
                            | Copysign => SOME (if c1.Sign = c2.Sign then c1 else (float_negate c1)))`

val _ = Define
`app_testop_i testop c = (case testop of Eqz => w2n c = 0)`

val _ = Define
  `app_relop_i rop c1 c2 = (case rop of
                              Eq => c1 = c2
                            | Ne => c1 <> c2
                            | Lt U => word_lt c1 c2
                            | Lt S => w2i c1 < w2i c2
                            | Gt U => word_gt c1 c2
                            | Gt S => w2i c1 > w2i c2
                            | Le U => word_le c1 c2
                            | Le S => w2i c1 <= w2i c2
                            | Ge U => word_ge c1 c2
                            | Ge S => w2i c1 >= w2i c2)`

val _ = Define
  `app_relop_f rop c1 c2 = (case rop of
                              Eqf => float_equal c1 c2
                            | Nef => ~float_equal c1 c2
                            | Ltf => float_less_than c1 c2
                            | Gtf => float_greater_than c1 c2
                            | Lef => float_less_equal c1 c2
                            | Gef => float_greater_equal c1 c2)`

val typeof_def = Define `
  typeof v = case v of ConstInt32   _ => T_i32
                     | ConstInt64   _ => T_i64
                     | ConstFloat32 _ => T_f32
                     | ConstFloat64 _ => T_f64
`

val types_agree_def = Define `types_agree t v = (typeof v = t)`

(* 2.4.6  Expressions *)
val _ = Datatype `expr = Expr (instr list)`

(* 2.5  Modules *)
(* The definition of module is at the end of the section. *)

(* 2.5.1  Indices [moved-up] *)

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
val _ = Datatype `exportdesc =
        Export_func funcidx
      | Export_table tableidx
      | Export_mem memidx
      | Export_global globalidx`

val _ = Datatype `export = <| name: name; desc: exportdesc |>`

(* 2.5.11  Imports *)
val _ = Datatype `importdesc =
        Import_func typeidx
      | Import_table tabletype
      | Import_mem memtype
      | Import_global globaltype`

val _ = Datatype `import = <| module: name; name: name; desc: importdesc |>`

val _ = Datatype `module = <|
  types:   functype vec;
  funcs:   func     vec;
  tables:  table    vec;
  mems:    mem      vec;
  globals: global   vec;
  elem:    elem     vec;
  data:    data     vec;
  start:   start    option;
  imports: import   vec;
  exports: export   vec
|>`

val _ = export_theory()
