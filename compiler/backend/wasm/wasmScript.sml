(* This theory is based on
 *
 *   WebAssembly Core Specification
 *   W3C First Public Working Draft, 15 February 2018
 *
 * which is available at
 *
 *  https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/
 *
 * At the time of writing (August 2018), the version
 * above is not significantly outdated. To compare
 * against the most current version, see
 *
 *  https://github.com/WebAssembly/spec/compare/fpwd...master
 *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasm";

val _ = Datatype `ne_list = Base 'a | Conz 'a ne_list`

val to_list_def = Define `
  (to_list (Base a) = [a]) /\
  (to_list (Conz a y) = (a :: (to_list y)))`

val ne_list_last_length = store_thm(
  "ne_list_last_length",
  ``!(isne: 'a ne_list). (to_list isne) <> []``,
  Cases_on `isne` >> rw[to_list_def]
);

val _ = (* Immediate *)
  type_abbrev("i", ``:num``)

val _ = (* Static Offset *)
  type_abbrev("off", ``:num``)

val _ = (* Alignment Exponent *)
  type_abbrev("a", ``:num``)

(* 2.2.2  Integers *)
val _ = type_abbrev("u32", ``:32 word``)
val _ = type_abbrev("i32", ``:u32``)
val _ = type_abbrev("u64", ``:64 word``)
val _ = type_abbrev("i64", ``:u64``)

(* 2.2.3 Floating-Point *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#floating-point%E2%91%A0 *)
val _ = type_abbrev("f32", ``:( 8, 23) float``)
val _ = type_abbrev("f64", ``:(11, 52) float``)

(* 2.3.1  Value Types *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#value-types%E2%91%A0 *)
val _ = Datatype `valtype = T_i32 | T_i64 | T_f32 | T_f64`

(* 2.3.1.1  Conventions *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#conventions%E2%91%A6 *)
val _ = type_abbrev("t", ``:valtype``)
val bit_width_def = Define
  `bit_width t = case t of T_i32 => 32
                         | T_i64 => 64
                         | T_f32 => 32
                         | T_f64 => 64`

val _ = Datatype
  `tp = Tp_i8 | Tp_i16 | Tp_i32`

val t_length_def = Define
  `t_length t = case t of T_i32 => 4
                        | T_i64 => 8
                        | T_f32 => 4
                        | T_i64 => 8`

val tp_length_def = Define
  `tp_length t = case t of Tp_i8  => 1
                         | Tp_i16 => 2
                         | Tp_i32 => 4`

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

(* 2.3.3  Function Types *)
val _ = Datatype `functype = Tf (t list) (t list)`
val _ = set_mapped_fixity {tok = "_>", fixity = Infixr 700, term_name = "Tf"}

(* 2.3.7  Global Types *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#global-types%E2%91%A0 *)
val _ = Datatype `mut = T_const | T_var`
val _ = Datatype `globaltype = <| mut : mut ; t : valtype |>`

val is_var_def = Define
`is_var gt = (gt.mut = T_var)`

val _ = Datatype `t_context = <|
    types_t : tf list;
    func_t  : tf list;
    global  : globaltype list;
    table   : num option;
    memory  : num option;
    local   : t list;
    label   : (t list) list;
    return  : (t list) option |>`

val _ = Datatype `s_context = <|
         s_inst  : t_context list;
         s_funcs : functype list       ;
         s_tab   : num list      ;
         s_mem   : num list      ;
         s_globs : globaltype list       |>`

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

val _ = Datatype
  `const = Const valtype`

val _ = Datatype `memarg = <| offset: word32; align: word32 |>`

(* 2.5.1  Indices *)
val _ = type_abbrev("typeidx", ``:word32``)
val _ = type_abbrev("funcidx", ``:word32``)
val _ = type_abbrev("tableidx", ``:word32``)
val _ = type_abbrev("memidx", ``:word32``)
val _ = type_abbrev("globalidx", ``:word32``)
val _ = type_abbrev("localidx", ``:word32``)
val _ = type_abbrev("labelidx", ``:word32``)

val _ = Datatype `instr =
(* 2.4.1  Numeric Instructions *)
  Const valtype
| Unop_i t iunop
| Unop_f t funop
| Binop_i t ibinop
| Binop_f t fbinop
| Testop_i t itestop
| Relop_i t irelop
| Relop_f t frelop
| Cvtop t cvtop t (sx option)

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
         | Store t (tp option) memarg
         | Current_memory
         | Grow_memory

(* 2.4.5  Control Instructions *)
         | Unreachable
         | Nop
         | Block functype (instr list)
         | Loop functype (instr list)
         | If functype (instr list) (instr list)
         | Br labelidx
         | Br_if labelidx
         | Br_table (labelidx ne_list) labelidx
         | Return
         | Call funcidx
         | Call_indirect typeidx`

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

val _ = Datatype `
  v = ConstInt32   i32
    | ConstInt64   i64
    | ConstFloat32 f32
    | ConstFloat64 f64
`

val typeof_def = Define `
  typeof v = case v of ConstInt32   _ => T_i32
                     | ConstInt64   _ => T_i64
                     | ConstFloat32 _ => T_f32
                     | ConstFloat64 _ => T_f64
`

val types_agree_def = Define `types_agree t v = (typeof v = t)`

(* val _ = type_abbrev("meminst", ``:(b list)``) *)

(* 4  Execution *)

(* 4.2  Runtime Structure *)

(* 4.2.4  Addresses *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#addresses%E2%91%A0 *)
val _ = type_abbrev("addr", ``:num``)
val _ = type_abbrev("funcaddr", ``:addr``)
val _ = type_abbrev("tableaddr", ``:addr``)
val _ = type_abbrev("memaddr", ``:addr``)
val _ = type_abbrev("globaladdr", ``:addr``)

(* 4.2.11  External Values *)
(* Moved up since exportinst needs externval *)
val _ = `externval = Func funcaddr | Table tableaddr | Mem memaddr | Global globalalddr`

(* 4.2.10  Export Instances *)
(* Moved up since moduleinst needs exportinst. *)
val _ = `exportinst = <| name: name; value: externval |>`

(* 4.2.5  Module Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#module-instances%E2%91%A0 *)
val _ = Datatype
`moduleinst = <|
            types : functype list;
         funcaddrs : funcaddr list   ;
         tableaddrs   : tableaddr list ;
         memaddrs   : memaddr list ;
         globaladdrs : globaladdr list ;
         exports : exportinst list
                              |>`

(* 4.2.6  Function Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#function-instances%E2%91%A0 *)
val _ = Datatype
  `funcinst = <| type: functype; module: moduleinst; code func |>`
(* TODO: Host Functions *)

(* 4.2.7  Table Instances *)
val _ = Datatype `funcelem = funcaddr option`
val _ = Datatype `tableinst = <| elem: (funcelem list); max: u32 |>`

(* 4.2.9  Global Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#global-instances%E2%91%A0 *)
val _ = Datatype
  `globalinst = <| value: v; mut: mut |>`

val globalinst_is_var_def = Define
  `globalinst_is_var g = (g.mut = T_var)`

(* 3  Validation *)
(* 3.1.1  Contexts *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#contexts%E2%91%A0 *)
val _ = Datatype `context = <|
  types: (functype list);
         funcs: (functype list); tables: (tabletype list); mems: (memtype list); globals (globaltype list); locals (localtype list); labels: (resulttype list); return: (resulttype option) |>`

(* 3.2  Types *)

(* 3.3  Instructions *)

val _ = Datatype
  `s = <|
         inst  : (inst list); (* *)
         funcs : (('host cl) list);
         tab   : (('host tabinst) list);
         mem   : ('meminst list);
         globs : (globaltype list)
       |>`


val stypes_def = Define
  `stypes s i j = EL j ((EL i s.inst).types)`

val sfunc_ind_def = Define
  `sfunc_ind s i j = EL j inst.funcs (EL i s.inst).funcs`

(* sfunc, sglob_ind, sglob, sglob_val, stab_s, stab *)

(* stab_unfold *)

(* supdate_glob_s, supdate_glob *)

val _ = Datatype (* Administrative Operators *)
  `e = Basic (('a, 'b, 'c, 'd) b_e)
     | Trap
     | Callcl (('a, 'b, 'c, 'd, 'host) cl)
     | Label num (e list) (e list)
     | Local num i ((('a, 'b, 'c, 'd) v) list) (e list)`

(* NOTE: $ is not overloaded to Basic since $ is already taken. *)
(* inj_basic, inj_basic_econst *)

val is_const_def = Define
`is_const e = case e of (Basic (EConst _)) => T | _ => F`

val const_list_def = Define
  `const_list xs = FILTER is_const xs`

val _ = Datatype
`Lholed = LBase ((('a, 'b, 'c, 'd, 'host) e) list) ((('a, 'b, 'c, 'd, 'host) e) list)
        | LRec ((('a, 'b, 'c, 'd, 'host) e) list) num ((('a, 'b, 'c, 'd, 'host) e) list) Lholed ((('a, 'b, 'c, 'd, 'host) e) list)`

(* TODO: locale wasm_memory_base ... How to translate "locale"? *)
(* TODO: locale wasm_typing *)
(* TODO: to_e_list[_{1,2,3}] *)

(* NOTE: $* is not overloaded to to_e_list since $ is already taken. *)
val _ = overload_on("to_e_list", ``MAP Basic``)

(* NOTE: $$* is not overloaded to v_to_e_list since $ is already taken. *)
val _ = overload_on("v_to_e_list", ``MAP (\x. Basic C x)``)

(* TODO: v_exists_b_e *)

(* TODO: Lfilled, Lfilled_exact and related lemmas ... How to translate "inductive"? *)

(* TYPING RELATION *)

val load_store_t_bounds_def = Define
  `load_store_bounds a tp t = case tp of NONE => 2 ** a <= t_length t
        | SOME tp => (2 ** a <= tp_length tp /\ tp_length tp <= t_length t /\ is_int_t t)`

(* be_typing, cl_typing, e_typing *)
(*
val _ = Define `
 opt_word x sx = (case x of SOME y => SOME (case sx of U => x | S => ) | _ => NONE)`

val _ = Define `float_incomp x y = (float_compare x y = UN)`

val _ = Define `float_strange x = float_incomp x x`

val _ = Define `
  cvt_i32 sx v = (case v of
                   ConstInt32 c => NONE
                 | ConstInt64 c => SOME (wasm_wrap c)
                 | ConstFloat32 c => (case sx of
                                      SOME U => NONE (* float_to_int roundTowardZero c *)
                                    | SOME S => NONE (* float_to_int roundTowardZero c *)
                                    | NONE => NONE)
                 | ConstFloat64 c => (case sx of
                                      SOME U => NONE (* ui32_trunc_f64 c *)
                                    | SOME S => NONE (* si32_trunc_f64 c *)
                                    | NONE => NONE))`

val _ = Define `
  cvt_i64 sx v = (case v of
                   ConstInt32 c => (case sx of
                                      SOME U => SOME c:i64
                                    | SOME S => SOME (n2w (Num (w2i c))):i64
                                    | NONE => NONE)
                 | ConstInt64 c => NONE
                 | ConstFloat32 c => (case sx of
                                      SOME U => NONE (* ui64_trunc_f32 c *)
                                    | SOME S => NONE (* si64_trunc_f32 c *)
                                    | NONE => NONE)
                 | ConstFloat64 c => (case sx of
                                      SOME U => (* ui64_trunc_f64 c *)
                                    | SOME S => (* si64_trunc_f64 c *)
                                    | NONE => NONE))`

val _ = Define `
  cvt_f32 sx v = (case v of
                   ConstInt32 c => (case sx of
                                    SOME U => SOME (f32_convert_ui32 c)
                                  | SOME S => SOME (f32_convert_si32 c)
                                  | _ => NONE)
                 | ConstInt64 c => (case sx of
                                    SOME U => SOME (f32_convert_ui64 c)
                                  | SOME S => SOME (f32_convert_si64 c)
                                  | _ => NONE)
                 | ConstFloat32 c => NONE
                 | ConstFloat64 c => SOME (wasm_demote c))`

val _ = Define `
  cvt_f64 sx v = (case v of
                   ConstInt32 c => (case sx of
                                    SOME U => SOME (f64_convert_ui32 c)
                                  | SOME S => SOME (f64_convert_si32 c)
                                  | _ => NONE)
                 | ConstInt64 c => (case sx of
                                    SOME U => SOME (f64_convert_ui64 c)
                                  | SOME S => SOME (f64_convert_si64 c)
                                  | _ => NONE)
                 | ConstFloat32 c => SOME (wasm_promote c)
                 | ConstFloat64 c => NONE)`

val _ = Define `
  cvt t sx v = (case t of
                 T_i32 => (case (cvt_i32 sx v) of SOME c => SOME (ConstInt32 c) | NONE => NONE)
               | T_i64 => (case (cvt_i64 sx v) of SOME c => SOME (ConstInt64 c) | NONE => NONE)
               | T_f32 => (case (cvt_f32 sx v) of SOME c => SOME (ConstFloat32 c) | NONE => NONE)
               | T_f64 => (case (cvt_f64 sx v) of SOME c => SOME (ConstFloat64 c) | NONE => NONE))`
*)
val _ = export_theory();
