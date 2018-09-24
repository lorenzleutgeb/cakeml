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
 *)

open preamble wasmSemanticPrimitivesTheory

(* Needed for module instantiation. *)
open wasmStaticSemTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSem"

(* Auxiliary: *)
val OPTION_DEFAULT = Define `OPTION_DEFAULT NONE x = x /\ OPTION_DEFAULT (SOME y) x = y`

(* For integration with CakeML we define a state which subsumes a configuration,
 * since it contains a store and the the (intermediate) result and stack of the
 * only thread, i.e. its code.
 * Once threads become available in WebAssembly, see
 *  https://github.com/WebAssembly/threads
 * one may want to add this indirection here by moving frame and code
 * into a separate collection, and adding events. *)
val _ = Datatype `
  state =
    <| ffi:   'ffi ffi_state
     ; store: store
     ; frame: frame
     ; code:  code
     ; clock: num
     |>`

val state_empty_def = Define `state_empty f c s =
  <| ffi  := f
   ; store:= s
   ; frame:= frame_empty
   ; code := ([], [])
   ; clock:= c
   |>`

val expand_def = Define `
  expand s vs es =
    let c = (vs, es ++ (TL (SND s.code))) in
      if (ainstr2_size (SND c)) < (ainstr2_size (SND s.code))
      then (NONE, s with code := c)
      else
        if s.clock = 0
        then (SOME Timeout, s)
        else (NONE, s with <| code := c; clock := s.clock - 1 |>)`

(* Showing that expand ensures some lexicographic order helps for
 * termination proof of wasm_evaluate below. *)
val expand_dec = Q.store_thm("expand_dec[simp]",
 `expand s vs es = (NONE, s') ==> (($< LEX $<) (s'.clock, ainstr2_size (SND s'.code)) (s.clock, ainstr2_size (SND s.code)))`,
  rw[expand_def] >> simp [expand_def,pairTheory.LEX_DEF] >> rw [expand_def] >> simp [expand_def,LEX_DEF]
)

val expand_eq_none = Q.store_thm("expand_eq_none[simp]",
  `  s.code = (vs, es) /\ (s.clock > 0 \/ ainstr2_size (es' ++ (TL es)) < ainstr2_size es)
   ==>
     (?s'. (expand s vs' es' = (NONE, s') /\ s'.code = (vs', es' ++ (TL es))))`,
  rw [expand_def]
)

val effect_def = Define `effect s vs e = expand s vs [e]`

val resulting_def = Define `resulting s vs' = expand s vs' []`

val typ_assert_def = Define `
  typ_assert msg cond (r, s) = ((if cond then r else SOME (TypeError msg)), s)`

val typ_assert_eq_none = Q.store_thm("typ_assert_eq_none[simp]",
  `typ_assert msg c p = (NONE, s') <=> c /\ p = (NONE, s')`,
  Cases_on `p` >> simp [AllCaseEqs (), typ_assert_def] >> metis_tac []
)

val evaluate_nomatch_def = Define `
  evaluate_nomatch s = (SOME (TypeError "No reduction rule applicable. Stack does not match."), s)`

val evaluate_nomatch_eq_none = Q.store_thm("evaluate_nomatch_eq_none[simp]",
  `evaluate_nomatch s <> (NONE, s')`,
  simp[evaluate_nomatch_def]
)

(* NOTE: We assume that any host function corresponding to a
 * foreign functionis of type [i32] ^ 4 -> []. *)
val match_ffi_args_def = Define `
  match_ffi_args vs = case vs of
    | V_i32 len2 :: V_i32 ptr2 :: V_i32 len1 :: V_i32 ptr1 :: vs' =>
      (SOME (((w2n ptr1, w2n len1), (w2n ptr2, w2n len2)), vs'))
    | _ =>
      NONE`

val check_args_def = Define `check_args (Tf ts rts) vs = LIST_REL (\t v. t = typeof v) ts vs`

val state_order_quot = `inv_image ($< LEX $<) (\s. (s.clock, ainstr2_size (SND s.code)))`
val state_order_def = Define `state_order = inv_image ($< LEX $<) (\s. (s.clock, ainstr2_size (SND s.code)))`

val size_and_lex = [wasmSemanticPrimitivesTheory.ainstr_size_def, pairTheory.LEX_DEF, state_order_def]

(* NOTE: Traps are not bubbled up through reductions but returned directly! *)
val evaluate_small_def = tDefine "evaluate_small" `
  evaluate_small s = case s.code of
    | vs, NIL => (SOME (wrap_result vs), s)
    | vs, (e::es) => case (vs, e) of
      | vs, Plain pe => (case (vs, pe) of

        (* 4.4.1  Numeric Instructions *)

        (* 4.4.1.1 *)
        (* This rule is not in the spec since values are represented by constants there. *)
        | vs, Const v =>
          resulting s (v :: vs)

        (* 4.4.1.2 *)
        | V_i32 c :: vs', Unop_i W32 op =>
          resulting s ((V_i32 (app_unop_i op c)) :: vs')
        | V_i64 c :: vs', Unop_i W64 op =>
          resulting s ((V_i64 (app_unop_i op c)) :: vs')
        | V_f32 c :: vs', Unop_f W32 op =>
          resulting s ((V_f32 (app_unop_f op c)) :: vs')
        | V_f64 c :: vs', Unop_f W64 op =>
          resulting s ((V_f64 (app_unop_f op c)) :: vs')

        (* 4.4.1.3 *)
        | V_i32 c1 :: V_i32 c2 :: vs', Binop_i W32 op =>
          let vop = app_binop_i op c1 c2 in (case vop of
            | SOME c3 => resulting s (V_i32 c3 :: vs')
            | NONE    => (SOME (Trap "Undefined result for binary operation on i32"), s)
          )
        | V_i64 c1 :: V_i64 c2 :: vs', Binop_i W64 op =>
          let vop = app_binop_i op c1 c2 in (case vop of
            | SOME c3 => resulting s (V_i64 c3 :: vs')
            | NONE    => (SOME (Trap "Undefined result for binary operation on i64"), s)
          )
        | V_f32 c1 :: V_f32 c2 :: vs', Binop_f W32 op =>
          let vop = app_binop_f op c1 c2 in (case vop of
            | SOME c3 => resulting s (V_f32 c3 :: vs')
            | NONE    => (SOME (Trap "Undefined result for binary operation on f32"), s)
          )
        | V_f64 c1 :: V_f64 c2 :: vs', Binop_f W64 op =>
          let vop = app_binop_f op c1 c2 in (case vop of
            | SOME c3 => resulting s (V_f64 c3 :: vs')
            | NONE    => (SOME (Trap "Undefined result for binary operation on f64"), s)
          )

        (* 4.4.1.4 *)
        | V_i32 c :: vs', Testop_i W32 op =>
          resulting s ((wrap_bool (app_testop_i op c)) :: vs')
        | V_i64 c :: vs', Testop_i W64 op =>
          resulting s ((wrap_bool (app_testop_i op c)) :: vs')

        (* 4.4.1.5 *)
        | V_i32 c1 :: V_i32 c2 :: vs', Relop_i W32 op =>
          resulting s ((wrap_bool (app_relop_i op c1 c2)) :: vs')
        | V_i64 c1 :: V_i64 c2 :: vs', Relop_i W64 op =>
          resulting s ((wrap_bool (app_relop_i op c1 c2)) :: vs')
        | V_f32 c1 :: V_f32 c2 :: vs', Relop_f W32 op =>
          resulting s ((wrap_bool (app_relop_f op c1 c2)) :: vs')
        | V_f64 c1 :: V_f64 c2 :: vs', Relop_f W64 op =>
          resulting s ((wrap_bool (app_relop_f op c1 c2)) :: vs')

        (* 4.4.1.6 *)
        | v :: vs', Conversion c =>
          let vo = cvt c v in (case vo of
            | SOME v' => resulting s (v' :: vs')
            | NONE    => (SOME (Trap "Conversion error"), s)
          )

        (* 4.4.2  Parametric Instructions *)

        (* 4.4.2.1 *)
        | v :: vs', Drop =>
          resulting s vs'

        (* 4.4.2.2 *)
        | V_i32 0w :: v2 :: v1 :: vs', Select =>
          resulting s (v2 :: vs')
        | V_i32 i :: v2 :: v1 :: vs', Select =>
          resulting s (v1 :: vs')

        (* 4.4.3  Variable Instructions *)

        (* 4.4.3.1 *)
        | vs, Get_local x =>
          typ_assert "4.4.3.1.2" ((w2n x) < LENGTH s.frame.locals)
            (resulting s ((EL (w2n x) s.frame.locals) :: vs))

        (* 4.4.3.2 *)
        | v :: vs', Set_local x =>
          typ_assert "4.4.3.2.2" ((w2n x) < LENGTH s.frame.locals)
            (resulting (s with frame := (s.frame with locals := (LUPDATE v (w2n x) s.frame.locals))) vs')

        (* 4.4.3.3 *)
        | c :: vs', Tee_local x =>
          effect s (c :: c :: vs') (Plain (Set_local x))

        (* 4.4.3.4 *)
        | vs, Get_global x =>
          typ_assert "4.4.3.4.2" ((w2n x) < LENGTH s.frame.module.globaladdrs)
            (let a = EL (w2n x) s.frame.module.globaladdrs in
              typ_assert "4.4.3.4.4" (a < LENGTH s.store.globals)
                (resulting s ((EL a s.store.globals).value :: vs))
            )

        (* 4.4.3.5 *)
        | v :: vs', Set_global x =>
          typ_assert "4.4.3.5.2" ((w2n x) < LENGTH s.frame.module.globaladdrs)
            (let a = EL (w2n x) s.frame.module.globaladdrs in
              typ_assert "4.4.3.5.4" (a < LENGTH s.store.globals)
                (let glob = EL a s.store.globals in
                  typ_assert "Cannot set immutable global" (glob.mut = T_var)
                    (resulting (s with store := (s.store with globals := LUPDATE (glob with value := v) a s.store.globals)) vs')
                )
            )

        (* 4.4.4  Memory Instructions *)

        (* 4.4.4.1 *)
        | i :: vs', Load t ma =>
          (case mem_load_t s.store s.frame t ma i of
            | SOME v => resulting s (v :: vs')
            | NONE   => (SOME (Trap "Bad load instruction"), s)
          )
        | i :: vs', Loadi w sz sx ma =>
          (case mem_load_sz_sx s.store s.frame w sz sx ma i of
            | SOME v => resulting s (v :: vs')
            | NONE   => (SOME (Trap "Bad load instruction"), s)
          )

        (* 4.4.4.2 *)
        | i :: v :: vs', Store t ma =>
          (case mem_store_t s.store s.frame ma i v of
             | SOME s' => resulting (s with store := s') vs'
             | NONE => (SOME (Trap "Bad store instruction"), s))

        | i :: v :: vs', Storei w sz ma =>
          (case mem_store_sz s.store s.frame sz ma i v of
             | SOME s' => resulting (s with store := s') vs'
             | NONE => (SOME (Trap "Bad store instruction"), s))

        (* 4.4.4.3 *)
        | vs, MemorySize =>
          resulting s ((V_i32 (n2w (bytes_to_pages (LENGTH (get_mem s.store s.frame))))) :: vs)

        (* 4.4.4.4 *)
        (* NOTE: Growing memory always fails. That matches CakeML and makes it deterministic! *)
        | n :: vs', MemoryGrow =>
          resulting s ((V_i32 (i2w ~1)) :: vs')

        (* 4.4.5  Control Instructions *)

        (* 4.4.5.1 *)
        | vs, Nop =>
          resulting s vs

        (* 4.4.5.2 *)
        | vs, Unreachable =>
          (SOME (Trap "Unreachable"), s)

        (* 4.4.5.3 *)
        | vs, Block ts es' =>
          effect s vs (Label (LENGTH ts) [] ([], (MAP Plain es')))

        (* 4.4.5.4 *)
        | vs, Loop ts es' =>
          effect s vs (Label 0 [pe] ([], (MAP Plain es')))

        (* 4.4.5.5 *)
        | V_i32 0w :: vs', If t i1s i2s =>
          effect s vs' (Plain (Block t i2s))
        | V_i32 i :: vs', If t i1s i2s =>
          effect s vs' (Plain (Block t i1s))

        (* 4.4.5.6 *)
        | vs, Br k =>
          effect s [] (Breaking (w2n k) vs)

        (* 4.4.5.7 *)
        | V_i32 0w :: vs', Br_if l =>
          resulting s vs'
        | V_i32 i :: vs', Br_if l =>
          effect s vs' (Plain (Br l))

        (* 4.4.5.8 *)
        | V_i32 i :: vs', Br_table ls ln =>
          let nls = to_list ls in
          effect s vs' (Plain (Br (if w2n i < LENGTH nls then EL (w2n i) nls else ln)))

        (* 4.4.5.9 *)
        | vs, Return =>
          effect s [] (Returning vs)

        (* 4.4.5.10 *)
        | vs, Call x =>
          typ_assert "4.4.5.10.2" ((w2n x) < LENGTH s.frame.module.funcaddrs)
            (effect s vs (Invoke (EL (w2n x) s.frame.module.funcaddrs)))

        (* 4.4.5.11 *)
        | V_i32 i :: vs', Call_indirect x =>
          let tab = get_table s.store s.frame in
            typ_assert "4.4.4.5.11.10" ((w2n x) < LENGTH tab)
              (case EL (w2n i) tab of
                | NONE => (SOME (TypeError "4.4.5.11.11"), s)
                | SOME a =>
                  typ_assert "4.4.5.11.13" (a < LENGTH s.store.funcs)
                    if funcinst_type (EL a s.store.funcs) <> (EL (w2n x) s.frame.module.types)
                    then (SOME (Trap "4.4.5.11.16"), s)
                    else effect s vs' (Invoke a)
              )

        | vs, pe =>
          evaluate_nomatch s
      )

      (* 4.4.5.6 *)
      | vs, Label n is (vs', Breaking 0 r :: es') =>
        expand s ((TAKE n r) ++ vs) (MAP Plain is)
      | vs, Label n is (vs', Breaking k r :: es') =>
        effect s vs (Breaking (k - 1) r)

      (* 4.4.5.9 *)
      | vs, Label n is (vs', Returning r :: es') =>
        effect s vs (Returning r)
      | vs, Frame n f (vs', Returning r :: es') =>
        (NONE, s with code := ((TAKE n r) ++ vs, []))

      (* 4.4.6.2 *)
      (* Fall through from a label that has been fully reduced. *)
      | vs, Label n is (vs', []) =>
        resulting s (vs' ++ vs)

      (* 4.4.7.2 *)
      | vs, Frame n f (vs', []) =>
        resulting s (vs' ++ vs)

      (* 4.2.13.3 *)
      (* Recursion to evaluate what's inside a frame. *)
      | vs, Frame n f c =>
        (case evaluate_small (s with <| code := c; frame := f |>) of
          | SOME r, s' => (SOME r, s')
          | NONE  , s' => effect s vs (Frame n s'.frame s'.code)
        )

      (* Recursion to evaluate what's inside a label. *)
      | vs, Label n is c =>
        (case evaluate_small (s with code := c) of
          | SOME r, s' => (SOME r, s')
          | NONE  , s' => effect s vs (Label n is s'.code)
        )

      | vs, Breaking k r =>
        (SOME (TypeError "Undefined label"), s)

      (* 4.4.7.{1,3} *)
      | vs, Invoke a =>
        typ_assert "4.4.7.1.2" (a <= LENGTH s.store.funcs)
          (case (EL a s.store.funcs) of
            (* 4.4.7.1 *)
            | Native (Tf t1 t2) mi f => (
              let (n, m) = (LENGTH t1, LENGTH t2) in
              typ_assert "4.4.7.1.{4,7} (at least one of the two)" (m <= 1 /\ n <= LENGTH vs)
                (effect s (DROP n vs) (Frame
                  m
                  <| module := mi; locals := (TAKE n vs) ++ (MAP zero f.locals) |>
                  ([], [Plain (Block t2 (expr_to_instrs f.body))])
                ))
            )

            (* 4.4.7.3 *)
            | Host (ForeignFunction name) =>
              case match_ffi_args vs of
                | NONE => (SOME (TypeError "4.4.7.3"), s)
                | SOME (((ptr1, len1), (ptr2, len2)), vs') =>
                  let rbs = read_mem s.store s.frame in
                    case (rbs ptr1 len1, rbs ptr2 len2) of
                      | SOME b1s, SOME b2s => (case call_FFI s.ffi name b1s b2s of
                        | FFI_final outcome => (SOME (FinalFFI outcome), s)
                        | FFI_return new_ffi new_bytes => (case write_mem s.store s.frame ptr1 new_bytes of
                          | SOME s' => resulting (s with <| ffi := new_ffi; store := s' |>) vs'
                          | NONE    => (SOME (Trap "Host function wants to write out of bounds"), s)
                        )
                      )
                      | _ => (SOME (Trap "Host function arguments out of bounds"), s)
          )

      (* 4.5.4 *)
      | vs, Init_elem a i [] =>
        resulting s vs
      | vs, Init_elem a i (x0::xs) =>
        effect (s with store := (s.store with tables := LUPDATE_MAP (\x. x with elem := (LUPDATE (SOME (EL (w2n x0) s.frame.module.funcaddrs))) (w2n i) x.elem) a s.store.tables)) vs (Init_elem a (word_add i 1w) xs)

      | vs, Init_data a i [] =>
        resulting s vs
      | vs, Init_data a i (b0::bs) =>
        effect (s with store := (s.store with mems := LUPDATE_MAP (\x. x with data := (LUPDATE b0 (w2n i) x.data)) a s.store.mems)) vs (Init_data a (word_add i 1w) bs)

      | vs, es =>
        evaluate_nomatch s
`
(
  WF_REL_TAC state_order_quot >>
  simp size_and_lex
)

val evaluate_small_progress = Q.store_thm("evaluate_small_progress",
  `!s s'. evaluate_small s = (NONE, s') ==> state_order s' s`,
  ho_match_mp_tac (theorem "evaluate_small_ind") >> rpt gen_tac >> strip_tac >>
  Cases_on `s.code` >> rename [`s.code = (vs, es)`] >>
  Cases_on `es` >> ONCE_REWRITE_TAC [evaluate_small_def] >> simp [] >> rename [`s.code = (vs, e :: es)`] >>
  simp_tac (srw_ss () ++ boolSimps.COND_elim_ss) [AllCaseEqs (), PULL_EXISTS] >> rw [resulting_def,effect_def] >>
  TRY (drule expand_dec) >> simp size_and_lex
)

val evaluate_wasm_def = tDefine "evaluate_wasm" `
  evaluate_wasm s = case s.code of
    | vs, [] => (wrap_result vs, s)
    | vs, es => case evaluate_small s of
      | SOME r', s' => (r', s')
      | NONE   , s' => evaluate_wasm s'
`
(
  WF_REL_TAC state_order_quot >> rw []
  >> drule evaluate_small_progress >> simp size_and_lex
)

(* TODO:
 *  - Theorem that asserts translation of a fill_b match into Breaking ainstr.
 *  - Theorem that asserts transportation of a Breaking ainstr to the outside by removing blocks.
 *  - Theorem that asserts equal results for Breaking and a fill_b without any more layers.
 *)
(* val evaluate_small_fill_b_eq_breaking = Q.store_thm("evaluate_small_fill_b_eq_breaking", *)
(*   `(!vs vs' b s s'. *)
(*      vs = b_vals b /\ s.code = (vs', [Label (LENGTH vs) [] (fill_b b (Plain (Br (n2w (b_depth b)))))]) *)
(*    ==> *)
(*      evaluate_small s = (NONE, s') /\ s'.code = (vs', Label (LENGTH vs) [] (fill_b (Breaking (n2w (b_depth b)) vs'))) *)
(*    )`, *)
(*   cheat *)
(* ) *)

val evaluate_fill_b = Q.store_thm("evaluate_fill_b",
  `(!s vs is b.
      s.code = ([], [Label (LENGTH vs) [] (fill_b b (vs, [Plain (Br (n2w (b_depth b)))]))]) /\ LENGTH vs < 2 /\ s.clock > 0
    ==>
      (?s'. evaluate_wasm s = (wrap_result vs, s'))
   )`,
  rw [wasmSemanticPrimitivesTheory.wrap_result_def] >> imp_res_tac wasmSemanticPrimitivesTheory.wrap_result_eq_result >>

  Induct_on `b`
  >- (
    rpt gen_tac >> strip_tac >>
    fs [wasmSemanticPrimitivesTheory.fill_b_def,wasmSemanticPrimitivesTheory.b_depth_def] >>
    rename [`push_code p`] >> Cases_on `p` >>
    fs [wasmSemanticPrimitivesTheory.push_code_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    simp [effect_def,expand_def,wasmSemanticPrimitivesTheory.ainstr_size_def,listTheory.list_size_def,wasmLangTheory.instr_size_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >> simp [] >>
    rw [expand_def,wasmSemanticPrimitivesTheory.ainstr_size_def,listTheory.list_size_def,wasmLangTheory.instr_size_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >> simp [] >>
    (rw [listTheory.TAKE_APPEND1])
  )
  >- (
      rpt gen_tac >> strip_tac >> cheat
  )
)

val evaluate_fill_e = Q.store_thm("evaluate_fill_e",
  `  s.code = ([], [Frame (LENGTH vs) f (fill_b b (vs, [Plain Return]))]) /\ LENGTH vs < 2 /\ s.clock > 0
   ==>
     ? s'. evaluate_wasm s = (wrap_result vs, s')`,
  rw [wasmSemanticPrimitivesTheory.wrap_result_def] >> imp_res_tac wasmSemanticPrimitivesTheory.wrap_result_eq_result >>
  Induct_on `b`
  >- (
    rpt gen_tac >> strip_tac >>
    fs [wasmSemanticPrimitivesTheory.fill_b_def,wasmSemanticPrimitivesTheory.b_depth_def] >>
    rename [`push_code p`] >> Cases_on `p` >>
    fs [wasmSemanticPrimitivesTheory.push_code_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    simp [effect_def,expand_def,wasmSemanticPrimitivesTheory.ainstr_size_def,listTheory.list_size_def,wasmLangTheory.instr_size_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >>
    ONCE_REWRITE_TAC [evaluate_small_def] >> simp [] >>
    rw [expand_def,wasmSemanticPrimitivesTheory.ainstr_size_def,listTheory.list_size_def,wasmLangTheory.instr_size_def] >>
    ONCE_REWRITE_TAC [evaluate_wasm_def] >> simp [] >>
    (rw [listTheory.TAKE_APPEND1])
  )
  >- (
    rpt gen_tac >> strip_tac >> cheat
  )
)

(* TODO: Prove a theorem that for every constant expression there is a clock under which
 * it evaluates to a value. This should be helpful to prove stuff about initialization,
 * where constant expressions are evaluated to initialize globals. *)
(* val const_expr_evaluate_eq_timeout = Q.store_thm("const_expr_evaluate_eq_timeout" *)
(* `!is s. is_const_expr (Expr is) ==> (?ck. evaluate_wasm ())`, *)
(* ) *)

(* TODO: Do we need something like evaluate_expression? *)

(* 4.5.3  Allocation *)

(* 4.5.3.1  Functions *)
val allocfunc_def = Define `
  allocfunc s (f, m) =
    (s with funcs := s.funcs ++ [Native (EL (w2n f.type) m.types) m f], LENGTH s.funcs)
`

(* 4.5.3.2  Host Functions *)
(* Currently, FFIs are the only host functions that can be allocated. *)
val allochostfunc_foreignfunction_def = Define `
  allochostfunc_foreignfunction s ffi_name =
    (s with funcs := s.funcs ++ [Host (ForeignFunction ffi_name)], LENGTH s.funcs)
`

val LIST_MUL = Define `LIST_MUL l n = FUNPOW (APPEND l) n []`
val LIST_FILL = Define `LIST_FILL x n = LIST_MUL [x] n`

(* 4.5.3.3  Tables *)
val alloctable_def = Define `
  alloctable s (T_table tt et) =
    (s with tables := s.tables ++ [<| elem := LIST_FILL NONE (w2n tt.min); max := tt.max |>], LENGTH s.tables)
`

(* 4.5.3.4  Memories *)
val allocmem_def = Define `
  allocmem s mt =
    (s with mems := s.mems ++ [<| data := LIST_FILL 0w ((w2n mt.min) * page_size); max := mt.max |>], LENGTH s.mems)
`

(* 4.5.3.5  Globals *)
val allocglobal_def = Define `
  allocglobal s ((T_global mut valtype), v) =
    (s with globals := s.globals ++ [<| value := v; mut := mut |>], LENGTH s.globals)
`

(* 4.5.3.6  Growing Tables *)
val grow_ok_def = Define `
  growtable_ok t n = case t.max of
    | SOME m => if LENGTH t.elem + n < (w2n m) then SOME n else NONE
    | NONE   => SOME n
`

val growtable_def = Define `
  growtable t n = OPTION_MAP
    (\n. t with elem := t.elem ++ LIST_FILL NONE n)
    (growtable_ok t n)
`

(* 4.5.3.7  Growing Memories *)
val growmem_ok_def = Define `
  growmem_ok memi n = case memi.max of
    | SOME m => if (LENGTH memi.data) + (n * page_size) <= (w2n m) * page_size then SOME n else NONE
    | NONE   => SOME n
`

val growmem_def = Define `
  growmem memi n = OPTION_MAP
    (\n. memi with data := memi.data ++ (LIST_FILL 0w (n * page_size)))
    (growmem_ok memi n)
`

(* 4.5.3.8  Modules *)
val allocx_def = Define `
  allocx (f:store -> 'a -> (store # num)) s (xs:'a list) = FOLDR
    (\x (s, idxs). let (s', idx) = f s x in (s', idx::idxs))
    (s, [])
    xs
`

val moduleinst_from_imports_def = Define `
  moduleinst_from_imports (m: module) is =
    <| types       := m.types
     ; funcaddrs   := externval_funcs   is
     ; tableaddrs  := externval_tables  is
     ; memaddrs    := externval_mems    is
     ; globaladdrs := externval_globals is
     |>`

val create_export_def = Define `
  create_export (m:moduleinst) e = <| name := e.name; value := case e.desc of
  | Export_func   idx => Func   (EL (w2n idx) m.funcaddrs)
  | Export_table  idx => Table  (EL (w2n idx) m.tableaddrs)
  | Export_mem    idx => Mem    (EL (w2n idx) m.memaddrs)
  | Export_global idx => Global (EL (w2n idx) m.globaladdrs)
  |>`

val allocmodule_def = Define `
  allocmodule s (m:module) externalvals vs =
    let mi = moduleinst_from_imports m externalvals in
    let (s1,   funcaddrs) = allocx allocfunc   s  (MAP (\x. (x, mi)) m.funcs) in
    let (s2,  tableaddrs) = allocx alloctable  s1 (MAP (\x. x.type) m.tables) in
    let (s3,    memaddrs) = allocx allocmem    s2 (MAP (\x. x.type) m.mems) in
    let (s', globaladdrs) = allocx allocglobal s3 (ZIP ([](* (m: module).globals *), vs)) in
    let mi = mi with
      <|   funcaddrs := mi.funcaddrs   ++   funcaddrs
       ;  tableaddrs := mi.tableaddrs  ++  tableaddrs
       ;    memaddrs := mi.tableaddrs  ++  tableaddrs
       ; globaladdrs := mi.globaladdrs ++ globaladdrs
       |> in
    let mi = mi with exports := MAP (create_export mi) m.exports in
      (s', mi)
`

(* 4.5.5  Invocation *)
val _ = Datatype `invocation_result = Success (result # 'ffi state) | Failure`

val invoke_def = Define `
  invoke ffi clock (s:store) a vs =
    if LENGTH s.funcs < a then Failure else
    if ~(check_args (funcinst_type (EL a s.funcs)) vs) then Failure else
      Success (evaluate_wasm
        <| code  := (vs, [Invoke a])
         ; clock := clock
         ; store := s
         ; frame := frame_empty
         ; ffi   := ffi
         |>
       )`

val invoke_from_def = Define `invoke_from s = invoke s.ffi s.clock s.store`

val is_const_instr_moduleinst_def = Define `
is_const_instr_moduleinst mi s (Const cv) = T /\
is_const_instr_moduleinst mi s (Get_global x) = ((LENGTH mi.globaladdrs) < (w2n x) /\ (case (EL (EL (w2n x) mi.globaladdrs) s.globals).mut of T_const => T | _ => F)) /\
is_const_instr_moduleinst mi s i = F`

val is_const_expr_moduleinst_def = Define `is_const_expr mi s (Expr is) = (EVERY (is_const_instr_moduleinst mi s) is)`

(* For initialization we have expressions of the following types:
 *  - globals: [ t ]
 *  - elem:    [i32]
 *  - data:    [i32]
 * Therefore we expect a nonempty result. *)
val eval_const_expr_def = Define `
  eval_const_expr (s:'ffi state) f (Expr is) =
    if ~(is_const_expr f.module s.store (Expr is)) then NONE else
    let (r, s') = evaluate_wasm (s with code := ([], [Frame 0 f ([], (MAP Plain is))])) in
        case r of
         | Result (SOME r) => SOME r
         | _               => NONE
`

val init_elem_def = Define `
  init_elem s f m = OPT_MMAP
    (\x. OPTION_MAP  (\eo. Init_elem (w2n x.table) (val2w eo) x.init) (eval_const_expr s f x.offset)) m.elem
`

val init_data_def = Define `
init_data s f m = OPT_MMAP
  (\x. OPTION_MAP  (\eo. Init_data (w2n x.data) (val2w eo) x.init) (eval_const_expr s f x.offset)) m.data
`

val init_globals_def = Define `
  init_globals s f m = OPT_MMAP
    (\x. (eval_const_expr s f x.init)) m.globals
`

(* 4.5.4  Instantiation *)
val instantiate_def = Define `
  instantiate ffi clock stor (m:module) (imports: externval list) =
    let state = state_empty ffi clock stor in
    let minst = moduleinst_empty with globaladdrs := externval_globals imports in
    let frame = frame_empty with module := minst in
    case init_globals state frame m of
    | SOME vs =>
      let (s', minst) = allocmodule stor m imports vs in
      let frame = frame_empty with module := minst in
      let state = (state_empty ffi clock s') with frame := frame in
      let inite = init_elem state frame m in
      let initd = init_data state frame m in
      let start = OPTION_DEFAULT (OPTION_MAP (\x. [Invoke (w2n x.func)]) m.start) [] in
      case (inite, initd) of
      | (SOME eis, SOME dis) =>
        SOME (state with code := ([], eis ++ dis ++ start))
      | _ => NONE
    | _ => NONE
`

val import_to_ffi_name_def = Define `
  import_to_ffi_name (m:module) i =
    let module_name = ffi_module_name in
    case (i.module, i.desc) of
    | (module_name, Import_func ti) =>
      if (EL (w2n ti) m.types) = ffi_type then SOME (name_to_string i.name) else NONE
    | _ => NONE
`

val stub_ffis_def = Define `
  stub_ffis m =
    OPTION_MAP
      (\ffi_names.
        let (s', funcaddrs) = allocx allochostfunc_foreignfunction store_empty ffi_names in
          (s', MAP (\a. Func a) funcaddrs)
      )
      (OPT_MMAP (import_to_ffi_name m) m.imports)
`

val instantiate_with_stubbed_ffi = Define `
  instantiate_with_stubbed_ffi ffi clock m =
    OPTION_MAP
      (\ (s', externvals). instantiate ffi clock s' m externvals)
      (stub_ffis m)
`

(* TODO: Observational Semantics *)

val _ = export_theory()
