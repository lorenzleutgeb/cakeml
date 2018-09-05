(* NOTE: This theory is based on
 *
 *  WebAssembly Core Specification
 *  W3C First Public Working Draft, 15 February 2018
 *
 * which is available at
 *
 *  https://w3.org/tr/2018/wd-wasm-core-1-20180215/
 *
 * At the time of writing (August 2018), the version
 * above is not significantly outdated. To compare
 * against the most current version, see
 *
 *  https://github.com/webassembly/spec/compare/fpwd...master
 *
 * The ordering of definitions is meant to mirror the
 * original document. However, some exceptions were
 * made to have all definitions "straight forward".
 * These exceptions are marked with comments.
 *
 * This theory contains the small-step semantics, mostly
 * from Chapter 4 of the spec.
 *)

open preamble wasmSemanticPrimitivesTheory

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()
val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmRelSem"

val _ = Datatype `
  state =
    <| ffi: 'ffi ffi_state
     ; store:   store
     ; frame:   frame
     ; code:    code
     ; result: (result option)
     |>`

(* 4  Execution *)

(* NOTE: We define a number of reduction relations:
 *
 *       -s-> (from "simple")
 *       For rules that do not depend on the current store/frame
 *       but only operate on the stack.
 *
 *       -n-> (from "native")
 *       For rules that do depend on the current store/frame.
 *       This relation is the main one from the spec.
 *
 *       ---> and its refl. trans. closure --->*
 *       For rules that call host functions, to avoid a
 *       circular dependency between store and hostfunc.
 *
 *       expr -e->  expr  (from "expression")
 *       Similar to --->.
 *)

val wrap_option_def = Define `
wrap_option  NONE    msg vs es = (     vs, es, SOME (Trap msg)) /\
wrap_option (SOME v) msg vs es = (v :: vs, es, NONE           )`

val fine_def = Define `fine vs es = (vs, es, NONE)`

(* 4.4  Instructions *)

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-s->",
  term_name = "step_simple"
}
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "↝",
  term_name = "step_simple"
}
val (step_simple_rules, step_simple_cases, step_simple_ind) = Hol_reln `
(* 4.4.1.1 *)
(!vs es v. (vs, Const v, es) -s-> (fine (v :: vs) es)) /\
(* 4.4.1.2 *)
(!vs es c op. (V_i32 c :: vs, Unop_i W32 op, es) -s-> (fine ((V_i32 (app_unop_i op c)) :: vs) es)) /\
(!vs es c op. (V_i64 c :: vs, Unop_i W64 op, es) -s-> (fine ((V_i64 (app_unop_i op c)) :: vs) es)) /\
(!vs es c op. (V_f32 c :: vs, Unop_f W32 op, es) -s-> (fine ((V_f32 (app_unop_f op c)) :: vs) es)) /\
(!vs es c op. (V_f64 c :: vs, Unop_f W64 op, es) -s-> (fine ((V_f64 (app_unop_f op c)) :: vs) es)) /\
(* 4.4.1.3 *)
(!vs es c1 c2 op.
    (V_i32 c1 :: V_i32 c2 :: vs, Binop_i W32 op, es)
  -s->
    (wrap_option (OPTION_MAP V_i32 (app_binop_i op c1 c2)) "Binary operation without result" vs es)
) /\
(!vs es c1 c2 op.
    (V_i64 c1 :: V_i64 c2 :: vs, Binop_i W64 op, es)
  -s->
    (wrap_option (OPTION_MAP V_i64 (app_binop_i op c1 c2)) "Binary operation without result" vs es)
) /\
(!vs es c1 c2 op.
    (V_f32 c1 :: V_f32 c2 :: vs, Binop_f W32 op, es)
  -s->
    (wrap_option (OPTION_MAP V_f32 (app_binop_f op c1 c2)) "Binary operation without result" vs es)
) /\
(!vs es c1 c2 op.
    (V_f64 c1 :: V_f64 c2 :: vs, Binop_f W64 op, es)
  -s->
    (wrap_option (OPTION_MAP V_f64 (app_binop_f op c1 c2)) "Binary operation without result" vs es)
) /\
(* 4.4.1.4 *)
(!vs es c op. (V_i32 c :: vs, Testop_i W32 op, es) -s-> (fine (wrap_bool (app_testop_i op c) :: vs) es)) /\
(!vs es c op. (V_i64 c :: vs, Testop_i W64 op, es) -s-> (fine (wrap_bool (app_testop_i op c) :: vs) es)) /\
(* 4.4.1.5 *)
(!vs es c1 c2 op.
    (V_i32 c1 :: V_i32 c2 :: vs, Relop_i W32 op, es)
  -s->
    (fine (wrap_bool (app_relop_i op c1 c2) :: vs) es)
) /\
(!vs es c1 c2 op.
    (V_i64 c1 :: V_i64 c2 :: vs, Relop_i W64 op, es)
  -s->
    (fine (wrap_bool (app_relop_i op c1 c2) :: vs) es)
) /\
(!vs es c1 c2 op.
    (V_f32 c1 :: V_f32 c2 :: vs, Relop_f W32 op, es)
  -s->
    (fine (wrap_bool (app_relop_f op c1 c2) :: vs) es)
) /\
(!vs es c1 c2 op.
    (V_f64 c1 :: V_f64 c2 :: vs, Relop_f W64 op, es)
  -s->
    (fine (wrap_bool (app_relop_f op c1 c2) :: vs) es)
) /\
(* 4.4.1.6 *)
(!vs es v c. (v :: vs, Conversion c, es) -s-> (wrap_option (cvt c v) "Conversion error" vs es)) /\
(* 4.4.2.1 *)
(!vs es. (v :: vs, Drop, es) -s-> (fine vs es)) /\
(* 4.4.2.2 *)
(!vs es a b i. (a :: b :: V_i32 i :: vs, Select, es) -s-> (fine ((if i = 0w then b else a) :: vs) es)) /\
(* 4.4.3.3 *)
(!vs es v x. (v :: vs, Tee_local x, es) -s-> (fine (v :: v :: vs) (Plain (Set_local x) :: es))) /\
(* 4.4.5.1 *)
(!vs es. (vs, Nop, es) -s-> (fine vs es)) /\
(* 4.4.5.2 *)
(!vs es. (vs, Unreachable, es) -s-> (vs, es, SOME (Trap "Unreachable executed"))) /\
(* 4.4.5.3 *)
(!vs es t is. (vs, Block t is, es) -s-> (fine vs (Label (LENGTH t) [] ([], MAP Plain is) :: es))) /\
(* 4.4.5.4 *)
(!vs es t is. (vs, Loop  t is, es) -s-> (fine vs (Label 0 [Loop t is] ([], MAP Plain is) :: es))) /\
(* 4.4.5.5 *)
(!t i1s i2s i.
  (V_i32 i :: vs, If t is1 is2, es) -s-> (fine vs (Plain (Block t (if i = 0w then i2s else i1s)) :: es))
) /\
(* 4.4.5.7 *)
(!vs es b l.
  (V_i32 b :: vs, Br_if l, es) -s-> (fine vs ((if b = 0w then [] else [Plain (Br l)]) ++ es))
) /\
(* 4.4.5.8 *)
(!vs es i ls ln.
    (V_i32 (n2w i) :: vs, Br_table ls ln, es)
  -s->
    (fine vs (Plain (Br (if i < LENGTH (to_list ls) then EL i (to_list ls) else ln)) :: es))
)
`

(* Now, the steps that involve store and/or frame. *)
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-n->",
  term_name = "step_native"
}
val (step_native_rules, step_native_cases, step_native_ind) = Hol_reln `
(* 4.2.13.3 *)
(* (!s f' f'' n. (s, f', is) -n-> (s', f'', is', r) ==> (s, f, [Frame n f' is]) -n-> (s', f, [Frame n f'' is'], r)) /\ *)
(* 4.4.3.1 *)
(!vs es s f x. (s, f, (vs, Plain (Get_local (n2w x)) :: es)) -n-> (s, f, (EL x f.locals :: vs, es), NONE)) /\
(* 4.4.3.2 *)
(!vs es s f x v. (s, f, (v :: vs, Plain (Set_local (n2w x)) :: es)) -n-> (s, (f with locals := LUPDATE v x f.locals), (vs, es), NONE)) /\
(* 4.4.3.4 *)
(!vs es s f x. (s, f, (vs, Plain (Get_global (n2w x)) :: es)) -n-> (s, f, ((EL (EL x f.module.globaladdrs) s.globals).value :: vs, es), NONE)) /\
(* 4.4.3.5 *)
(!vs es s f x a v. a = EL x f.module.globaladdrs ==>
    (s, f, (v :: vs, Plain (Set_global (n2w x)) :: es))
  -n->
    (s with globals := LUPDATE ((EL a s.globals) with value := v) a s.globals, f, (vs, es), NONE)
) /\
(* 4.4.4.1 *)
(* First case, for Load without any further arguments. *)
(!vs es s f t i ma.
    (s, f, (i :: vs, Plain (Load t ma) :: es))
  -n->
    case mem_load_t s f t ma i of
      | NONE   => (s, f, (vs, es), SOME (Trap "Invalid load"))
      | SOME v => (s, f, (v :: vs, es), NONE)
) /\
(* Second case, for Load with storage size and sign extension. *)
(!vs es s f w sz sx ma.
    (s, f, (i :: vs, Plain (Loadi w sz sx ma) :: es))
  -n->
    case mem_load_sz_sx s f w sz sx ma i of
      | NONE   => (s, f, (vs, es), SOME (Trap "Invalid load"))
      | SOME v => (s, f, (v :: vs, es), NONE)
) /\
(* 4.4.4.2 *)
(* TODO *)
(* (!s f t v a w ma bs. (c = (s, f, [Const (V_i32 i); Const v; Store t NONE ma]) /\ a = HD f.module.memaddrs /\ t = typeof v /\ w = mem_write (EL a s.mems) i ma (bit_width t) v) ==> *)
(*     (w = NONE    ==> c -n-> (s, f, [Trap])) /\ *)
(*     (w = SOME bs ==> c -n-> (s with mems := LUPDATE a (m with data := bs) s.mems), f, []) *)
(* ) /\ *)
(* 4.4.4.3 *)
(!vs es s f. (s, f, (vs, Plain Current_memory :: es)) -n-> (s, f, ((V_i32 (n2w (bytes_to_pages (LENGTH (EL (HD f.module.memaddrs) s.mems).data)))) :: vs, es), NONE)) /\
(* 4.4.5.6 *)
(* NON PLAIN *)
(* (!vs es is l holed vs'. *)
(*     (vs, Label (LENGTH vs) is (fill_b l holed (vs', [Plain (Br (n2w l))])), es) *)
(*   -s-> *)
(*     (fine (vs' :: vs) ((MAP Plain is) ++ es)) *)
(* ) /\ *)
(* 4.4.5.9 *)
(!s f vs k.
    (s, f, (vs, Frame (LENGTH vs') f (fill_b b k (vs', [Plain Return])) :: es))
  -n->
    (s, f, (vs' ++ vs, es), NONE)
) /\
(* 4.4.6.2 *)
(* NON PLAIN *)
(* (!vs es n is vs'. (vs, Label n is (vs', []), es) -s-> (fine (vs' ++ vs) es)) *)
(* 4.4.5.10 *)
(!vs es s f x. (s, f, (vs, Plain (Call (n2w x)) :: es)) -n-> (s, f, (vs, Invoke (EL x f.module.funcaddrs) :: es), NONE)) /\
(* 4.4.5.11 *)
(!vs es s f x i a.
    (s, f, (V_i32 (n2w i) :: vs, Plain (Call_indirect (n2w x)) :: es))
  -n->
    if has (EL (HD f.module.tableaddrs) s.tables).elem i (SOME a) /\ has f.module.types x (funcinst_type (EL a s.funcs))
    then (s, f, (vs, Invoke a :: es), NONE)
    else (s, f, (vs, es), SOME (Trap "Invalid Call_indirect"))
) /\
(* 4.4.7.1 *)
(!s f a t1s t2s m mod code. (has s.funcs a (Native (t1s _> t2s) mod code)) /\ ts = code.locals /\ Expr is = code.body /\ m = LENGTH t2s /\ n = LENGTH t1s ==>
    (s, f, (vs, Invoke a :: es))
  -n->
    (s, f, (DROP n vs, (Frame m <| module := mod; locals := (TAKE n vs) ++ (MAP zero ts) |> ([], [Plain (Block t2s is)])) :: es), NONE)
) /\
(* 4.4.7.2 *)
(!vs es s f vs'. (s, f, (vs, Frame (LENGTH vs') f (vs', []) :: es)) -n-> (s, f, (vs' ++ vs, es), NONE))
`

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "--->",
  term_name = "step"
}
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "↪",
  term_name = "step"
}
val (step_rules, step_cases, step_ind) = Hol_reln `
(* lift -s-> *)
(!vs es s i vs' es' r. ((s.code = (vs, Plain i :: es)) /\ (s.result = NONE /\ (vs, i, es) -s-> (vs', es', r))) ==> s ---> (s with <| code := (vs', es'); result := r |>)) /\
(* lift -n-> *)
(!s s' f' c' r. (s.result = NONE /\ (s.store, s.frame, s.code) -n-> (s', f', c', r)) ==> s ---> (s with <| store := s'; frame := f'; code := (vs, es); result := r |>))
(* 4.4.7.3 *)
`

(* val _ = set_mapped_fixity { *)
(*   fixity    = Infix(NONASSOC, 450), *)
(*   tok       = "-e->", *)
(*   term_name = "step_expr" *)
(* } *)
(* val _ = Hol_reln ` *)
(* (!s f is s' f' is'. s, f, is) ---> (s', f', is') ==> *)
(*     (s, f, Expr is) -e-> (s', f', Expr is') *)
(* )` *)

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "--->*",
  term_name = "step_closure"
}
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "↪*",
  term_name = "step_closure"
}
val (step_closure_rules, step_closure_cases, step_closure_ind) = Hol_reln `(!a. a --->* a) /\ (!a b c. (a ---> b /\ b ---> c) ==> (a --->* c))`

val _ = export_theory ()
