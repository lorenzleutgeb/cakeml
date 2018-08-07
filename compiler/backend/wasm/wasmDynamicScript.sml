(* NOTE: Please consult README.md *)


open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmStaticTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmDynamic";

(*
val _ = Datatype
  `s = <|
         instr  : (instr list); (* *)
         funcs : (('host cl) list);
         tab   : (('host tabinst) list);
         mem   : ('meminst list);
         globs : (globaltype list)
       |>`

val stypes_def = Define
  `stypes s i j = EL j ((EL i s.inst).types)`

val sfunc_ind_def = Define
  `sfunc_ind s i j = EL j inst.funcs (EL i s.inst).funcs`
*)
(* sfunc, sglob_ind, sglob, sglob_val, stab_s, stab *)

(* stab_unfold *)

(* supdate_glob_s, supdate_glob *)

(* NOTE: $ is not overloaded to Basic since $ is already taken. *)
(* inj_basic, inj_basic_econst *)
(*
val is_const_def = Define
`is_const e = case e of (Const _) => T | _ => F`

val const_list_def = Define
  `const_list xs = FILTER is_const xs`

val _ = Datatype
`Lholed = LBase ((('a, 'b, 'c, 'd, 'host) e) list) ((('a, 'b, 'c, 'd, 'host) e) list)
        | LRec ((('a, 'b, 'c, 'd, 'host) e) list) num ((('a, 'b, 'c, 'd, 'host) e) list) Lholed ((('a, 'b, 'c, 'd, 'host) e) list)`
*)

(* TODO: locale wasm_memory_base ... How to translate "locale"? *)
(* TODO: locale wasm_typing *)
(* TODO: to_e_list[_{1,2,3}] *)

(* NOTE: $* is not overloaded to to_e_list since $ is already taken. *)
(*val _ = overload_on("to_e_list", ``MAP Basic``)*)

(* NOTE: $$* is not overloaded to v_to_e_list since $ is already taken. *)
(* val _ = overload_on("v_to_e_list", ``MAP (\x. Basic C x)``) *)

(* TODO: v_exists_b_e *)

(* TODO: Lfilled, Lfilled_exact and related lemmas ... How to translate "inductive"? *)

(* 4  Execution *)

(* 4.2  Runtime Structure *)

(* 4.2.1  Values [moved-up] *)

(* 4.2.2  Results *)
val _ = Datatype `result = Result (val list) | R_Trap`

(* 4.2.6  Function Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#function-instances%E2%91%A0 *)
(* Moved up since store needs funcinst. *)
val _ = Datatype
`funcinst = <| type: functype; module: moduleinst; code: func |>`
(* TODO: Host Functions *)

(* 4.2.7  Table Instances *)
(* Moved up since store needs tableinst. *)
val _ = Datatype `funcelem = Funcelem (funcaddr option)`
val _ = Datatype `tableinst = <| elem: funcelem list; max: u32 |>`

(* 4.2.8  Memory Instances *)
(* Moved up since store needs meminst. *)
val _ = Datatype `meminst = <| data: byte vec; max: u32 |>`

(* 4.2.9  Global Instances *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#global-instances%E2%91%A0 *)
(* Moved up since store needs globalinst. *)
val _ = Datatype
`globalinst = <| value: val; mut: mut |>`

(* 4.2.3  Store *)
val _ = Datatype `store = <|
  funcs:   funcinst   list;
  tables:  tableinst  list;
  mems:    meminst    list;
  globals: globalinst list
|>`

val globalinst_is_var_def = Define
  `globalinst_is_var g = (g.mut = T_var)`

(* 4.2.4  Adresses [moved-up] *)
(* 4.2.5  Module Instances [moved-up] *)
(* 4.2.6  Functions Instances [moved-up] *)
(* 4.2.7  Table Instances [moved-up] *)
(* 4.2.8  Memory Instances [moved-up] *)
(* 4.2.9  Global Instances [moved-up] *)
(* 4.2.10  Export Instances [moved-up] *)
(* 4.2.11  External Values [moved-up] *)

(* 4.2.12.2  Labels *)
val _ = Datatype `label = T_Label num (instr list)`

(* 4.2.12.3  Frames *)
(* Definition of frame was moved up. *)
val _ = `Datatype activation = Activation num frame`

(* 4.2.13  Administrative Instructions [moved-up] *)

(* 4.2.13.1  Block Contexts *)
val _ = Datatype `block = B0 (val list) (instr list) | Bk (val list) label block (instr list)`

val _ = Define `
(bc_apply (B0 vs is) js = (MAP Const vs) ++ (js ++ is)) /\
(bc_apply (Bk vs (T_Label n is) b is2) i = (MAP Const vs) ++ [Label n is (bc_apply b i ++ is2)])
`

(* 4.2.13.2  Configurations *)
val _ = Datatype `thread = Thread frame (instr list)`
val _ = Datatype `config = Config store thread`

(* 4.2.13.3  Evaluation Context *)
(* TODO: How to translate this? *)

(* 4.1.2  Formal Notation *)
(* Following operator shall correspond to the reduction rule operator. *)
val _ = set_mapped_fixity {
  fixity = Infix(NONASSOC, 450),
  tok = "-->",
  term_name = "redn"
}

(* 4.3  Numerics *)
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
