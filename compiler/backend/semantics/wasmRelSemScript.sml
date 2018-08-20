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

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmSemTheory patternMatchesLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSmallStepSem"

(* 4  Execution *)

(* NOTE: We define a number of reduction relations:
 *
 *       (instr list) -s-> (instr list)  (from "simple")
 *       For rules that do not depend on the current store/frame
 *       but only operate on the stack.
 *
 *       configuration ---> configuration
 *       For rules that do depend on the current store/frame.
 *       This relation is the main one from the spec.
 *
 *       state -c-> state  (from "complex")
 *       For rules that call host functions, to avoid a
 *       circular dependency between store and hostfunc.
 *
 *       expr -e->  expr  (from "expression")
 *       Similar to -s->.
 *)

(* Many steps operate only on the list of instructions
 * of the current thread. Since for these cases we do
 * not care about store and frame, we write them down
 * separately and lift them to the more general case
 * afterwards.
 *)

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
(* 4.2.13.3 *)
(!e. e <> E0 ==> fill_e e [Trap] -s-> [Trap]) /\
(!n f. [Frame n f [Trap]] -s-> [Trap]) /\
(* 4.4.1.2 *)
(!op v c. v = V_i32 c ==>
  [Const v; Unop_i W32 op] -s-> [Const (V_i32 (app_unop_i op c))]
) /\
(!op v c. v = V_i64 c ==>
  [Const v; Unop_i W64 op] -s-> [Const (V_i64 (app_unop_i op c))]
) /\
(!op v c. v = V_f32 c ==>
  [Const v; Unop_f W32 op] -s-> [Const (V_f32 (app_unop_f op c))]
) /\
(!op v c. v = V_f64 c ==>
  [Const v; Unop_f W64 op] -s-> [Const (V_f64 (app_unop_f op c))]
) /\
(* 4.4.1.3 *)
(!op c1 c2.
    (consts V_i32 [c1; c2]) ++ [Binop_i W32 op]
  -s->
    [wrap_option V_i32 (app_binop_i op c1 c2)]
) /\
(!op c1 c2.
    consts V_i64 [c1; c2] ++ [Binop_i W64 op]
  -s->
    [wrap_option V_i64 (app_binop_i op c1 c2)]
) /\
(!op c1 c2.
    [Const (V_f32 c1); Const (V_f32 c2); Binop_f W32 op]
  -s->
    [wrap_option V_f32 (app_binop_f op c1 c2)]
) /\
(!op c1 c2.
    [Const (V_f64 c1); Const (V_f64 c2); Binop_f W64 op]
  -s->
    [wrap_option V_f64 (app_binop_f op c1 c2)]
) /\
(* 4.4.1.4 *)
(!op c. [Const (V_i32 c); (Testop_i W32 op)] -s-> [wrap_bool (app_testop_i op c)]) /\
(!op c. [Const (V_i64 c); (Testop_i W64 op)] -s-> [wrap_bool (app_testop_i op c)]) /\
(* 4.4.1.5 *)
(!op c1 c2.
    [Const (V_i32 c1); Const (V_i32 c2); Relop_i W32 op]
  -s->
    [wrap_bool (app_relop_i op c1 c2)]
) /\
(!op c1 c2.
    [Const (V_i64 c1); Const (V_i64 c2); Relop_i W64 op]
  -s->
    [wrap_bool (app_relop_i op c1 c2)]
) /\
(!op c1 c2.
    [Const (V_f32 c1); Const (V_f32 c2); Relop_f W32 op]
  -s->
    [wrap_bool (app_relop_f op c1 c2)]
) /\
(!op c1 c2.
    [Const (V_f64 c1); Const (V_f64 c2); Relop_f W64 op]
  -s->
    [wrap_bool (app_relop_f op c1 c2)]
) /\
(* 4.4.1.6 *)
(!c v. [Const v; Conversion c] -s-> [wrap_option (\x.x) (cvt c v)]) /\
(* 4.4.2.1 *)
(!v. [Const v; Drop] -s-> []) /\
(* 4.4.2.2 *)
(!v a b. [a; b; wrap_bool v; Select] -s-> [if v then a else b]) /\
(* 4.4.3.3 *)
(!c x. [c; Tee_local x] -s-> [c; c; Set_local x]) /\
(* 4.4.5.1 *)
[Nop] -s-> [] /\
(* 4.4.5.2 *)
[Unreachable] -s-> [Trap] /\
(* 4.4.5.3 *)
(!t is. [Block t is] -s-> [Label (LENGTH t) [] is]) /\
(* 4.4.5.4 *)
(!t is. [Loop t is] -s-> [Label 0 [Loop t is] is]) /\
(* 4.4.5.5 *)
(!t i1s i2s v.
  [wrap_bool v; If t is1 is2] -s-> [Label (LENGTH t) [] (if v then i1s else i2s)]
) /\
(* 4.4.5.6 *)
(!is l vs. EVERY is_val vs ==>
  [Label (LENGTH vs) is (fill_b l holed (vs ++ [Br (n2w l)]))] -s-> vs ++ is
) /\
(* 4.4.5.7 *)
(!v l.
  [wrap_bool v; Br_if l] -s-> (if v then [Br l] else [])
) /\
(* 4.4.5.8 *)
(!i ls ln.
    [Const (V_i32 (n2w i)); Br_table ls ln]
  -s->
    [Br (if i < (LENGTH ls) then (EL i ls) else ln)]
) /\
(* 4.4.6.2 *)
(!n is vs. (EVERY is_val vs) ==> [Label n is vs] -s-> vs) /\
(* TODO: Conrad Watt also defines the following case. Not sure if needed? *)
(!n is. [Label n is [Trap]] -s-> [Trap])
`

(* Now, the steps that involve store and/or frame. *)
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
(!s f is is'. (is -s-> is') ==> (s, f, is) ---> (s, f, is')) /\
(* 4.2.13.3 *)
(!s f' f'' n. (s, f', is) ---> (s', f'', is') ==> (s, f, [Frame n f' is]) ---> (s', f, [Frame n f'' is'])) /\
(* 4.4.3.1 *)
(!s f x. (s, f, [Get_local (n2w x)]) ---> (s, f, [Const (EL x f.locals)])) /\
(* 4.4.3.2 *)
(!s f x v. (s, f, [Const v; Set_local (n2w x)]) ---> (s, (f with locals := LUPDATE v x f.locals), [])) /\
(* 4.4.3.4 *)
(!s f x. (s, f, [Get_global (n2w x)]) ---> (s, f, [Const (EL (EL x f.module.globaladdrs) s.globals).value])) /\
(* 4.4.3.5 *)
(!s f x a v. a = EL x f.module.globaladdrs ==>
    (s, f, [Const v; Set_global (n2w x)])
  --->
    (s with globals := LUPDATE ((EL a s.globals) with value := v) a s.globals, f, [])
) /\
(* 4.4.4.1 *)
(* First case, for Load without any further arguments. *)
(!s f t i ma. (s, f, [Const (V_i32 i); Load t NONE ma]) ---> (s, f, [wrap_option (bytes2val t) (mem_read (mem0 s f) i ma (bit_width t))])) /\
(* Second case, for Load with storage size and sign extension. *)
(!s f. (s, f, [Const (V_i32 i); Load t (SOME (sz, sx)) ma]) ---> (s, f, [wrap_option (bytes2val t) (mem_read (mem0 s f) i ma (bit_width_p sz))])) /\
(* 4.4.4.2 *)
(* TODO *)
(* (!s f t v a w ma bs. (c = (s, f, [Const (V_i32 i); Const v; Store t NONE ma]) /\ a = HD f.module.memaddrs /\ t = typeof v /\ w = mem_write (EL a s.mems) i ma (bit_width t) v) ==> *)
(*     (w = NONE    ==> c ---> (s, f, [Trap])) /\ *)
(*     (w = SOME bs ==> c ---> (s with mems := LUPDATE a (m with data := bs) s.mems), f, []) *)
(* ) /\ *)
(* 4.4.4.3 *)
(!s f. (s, f, [Current_memory]) ---> (s, f, [Const (V_i32 (n2w (bytes_to_pages (LENGTH (EL (HD f.module.memaddrs) s.mems).data))))])) /\
(* 4.4.5.9 *)
(!s f vs n k. (n = LENGTH vs) ==> (s, f, [Frame n f (fill_b b k (vs ++ [Return]))]) ---> (s, f, vs)) /\
(* 4.4.5.10 *)
(!s f x. (s, f, [Call (n2w x)]) ---> (s, f, [Invoke (EL x f.module.funcaddrs)])) /\
(* 4.4.5.11 *)
(!s f x i a.
    (s, f, [Const (V_i32 (n2w i)); Call_indirect (n2w x)])
  --->
    (s, f, if has (EL (HD f.module.tableaddrs) s.tables).elem i (SOME a) /\ has f.module.types x (funcinst_type (EL a s.funcs)) then [Invoke a] else [Trap])
) /\
(* 4.4.7.1 *)
(!s f a t1s t2s m mod code. (has s.funcs a (Native (t1s _> t2s) mod code)) /\ ts = code.locals /\ Expr is = code.body /\ m = LENGTH t2s ==>
    (s, f, (MAP Const vs) ++ [Invoke a])
  --->
    (s, f, [Frame m <| module := mod; locals := vs ++ (MAP zero t1s) |> [Block t2s is]])
) /\
(* 4.4.7.2 *)
(! s f n vs. n = LENGTH vs ==> (s, f, [Frame n f vs]) ---> (s, f, vs))
`

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-e->",
  term_name = "step_expr"
}
val _ = Hol_reln `
(!s f is s' f' is'. (s, f, is) ---> (s', f', is') ==>
  (s, f, Expr is) -e-> (s', f', Expr is')
)`

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-c->",
  term_name = "step_complex"
}
val (step_complex_rules, step_complex_cases, step_complex_ind) = Hol_reln `
(* lift ---> *)
(!hfs s s' f f' is is'. (s, f, is) ---> (s', f', is') ==> (hfs, (s, f, is)) -c-> (hfs, (s', f', is'))) /\
(* 4.4.7.3 *)
(* TODO: Ensure that s' extends s. *)
(* (!hfs s s' f hf t a r. has s.funcs a (Host t hf) /\ (EL hf hfs) s vs = (s', r) /\ arguments_ok vs t ==> *)
(*      (hfs, (s, f, (MAP Const vs) ++ [Invoke a])) *)
(*    -c-> *)
(*      (hfs, (s', f, [wrap_option (\x.x) r])) *)
(* ) *)
`

val _ = export_theory ()
