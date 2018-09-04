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
 *)

open preamble wasmSemanticPrimitivesTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSem"

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

(* TODO: There are multiple ad-hoc definitions of orderings floating around this file... *)

val code_order = Define `code_order = inv_image ($<) (\c. ainstr2_size (SND c))`

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
  rw[expand_def] >> simp [expand_def,LEX_DEF] >> rw [expand_def] >> simp [expand_def,LEX_DEF]
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

val wrap_result = Define `
wrap_result l = case LENGTH l of
                  | 0 => Result NONE
                  | 1 => Result (SOME (HD l))
                  | _ => TypeError "Expected result of at most one value"`

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
          (* Stack length remains unchanged, result length increases. *)
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
        | i :: vs', Loadi w tp sx ma =>
          (case mem_load_w_sx s.store s.frame w tp sx ma i of
            | SOME v => resulting s (v :: vs')
            | NONE   => (SOME (Trap "Bad load instruction"), s)
          )

        (* 4.4.4.2 *)
        (* TODO: Write a store function that avoids unbounded 'a word. *)
        (* | i :: v :: vs', Store t ma => *)
        (*   (case mem_store s.store s.frame (bit_width (typeof v)) ma i (val2w v) of *)
        (*      | SOME s' => resulting (s with store := s') vs' *)
        (*      | NONE => (SOME (Trap "Bad store instruction"), s)) *)

        (* | i :: v :: vs', Storei w tp ma => *)
        (*   (case mem_store s.store s.frame (bit_width_p tp) ma i (val2w v) of *)
        (*      | SOME s' => resulting (s with store := s') vs' *)
        (*      | NONE => (SOME (Trap "Bad store instruction"), s)) *)

        (* 4.4.4.3 *)
        | vs, Current_memory =>
          resulting s ((V_i32 (n2w (bytes_to_pages (LENGTH (get_mem s.store s.frame))))) :: vs)

        (* 4.4.4.4 *)
        (* NOTE: Growing memory always fails. That matches CakeML and makes it deterministic! *)
        | n :: vs', Grow_memory =>
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
          (* Same stack and result length, block is swapped for label. *)
          effect s vs (Label (LENGTH ts) [] ([], (MAP Plain es')))

        (* 4.4.5.4 *)
        | vs, Loop ts es' =>
          (* Same stack and result length, loop is swapped for label. *)
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

            | _ => (SOME (TypeError "TODO TODO TODO"), s)
            (* 4.4.7.3 *)
            (* NOTE: We assume that any host function is of type [i32] ^ 4 -> []. *)
            (* TODO: This case explodes. Assert i32^4 separately. *)
            (* | Host (ForeignFunction name) => (case vs of *)
            (*   | V_i32 (n2w len2) :: V_i32 (n2w ptr2) :: V_i32 (n2w len1) :: V_i32 (n2w ptr1) :: vs' => *)
            (*     let rbs = read_mem s.store s.frame in *)
            (*    case (rbs ptr1 len1, rbs ptr2 len2) of *)
            (*       | SOME b1s, SOME b2s => (case call_FFI s.ffi name b1s b2s of *)
            (*         | FFI_final outcome => (SOME (FinalFFI outcome), s) *)
            (*         | FFI_return new_ffi new_bytes => (case write_mem s.store s.frame ptr1 new_bytes of *)
            (*           | SOME s' => resulting (s with <| ffi := new_ffi; store := s' |>) vs' *)
            (*           | NONE    => (SOME (Trap "Host function wants to write out of bounds"), s) *)
            (*         ) *)
            (*       ) *)
            (*       | _ => (SOME (Trap "Host function arguments out of bounds"), s) *)
            (*   | _ => (SOME (TypeError "Host function expects four i32 arguments"), s) *)
            (* ) *)
          )

      (* 4.4.7.2 *)
      | vs, Frame n f (vs', []) =>
        resulting s (vs' ++ vs)

      | vs, es =>
        evaluate_nomatch s
`
(
  WF_REL_TAC `inv_image ($< LEX $<) (\s. (s.clock, ainstr2_size (SND s.code)))` >>
  simp [wasmSemanticPrimitivesTheory.ainstr_size_def]
)

val evaluate_small_progress = Q.store_thm("evaluate_small_progress",
  `!s s'. evaluate_small s = (NONE, s') ==> inv_image ($< LEX $<) (\s. (s.clock, ainstr2_size (SND s.code))) s' s`,
  ho_match_mp_tac (theorem "evaluate_small_ind") >> rpt gen_tac >> strip_tac >>
  Cases_on `s.code` >> rename [`s.code = (vs, es)`] >>
  Cases_on `es` >> ONCE_REWRITE_TAC [evaluate_small_def] >> simp [] >> rename [`s.code = (vs, e :: es)`] >>
  Cases_on `e` >> simp []
  >- (simp_tac (srw_ss () ++ boolSimps.COND_elim_ss) [AllCaseEqs (), PULL_EXISTS] >> rw[resulting_def,effect_def] >> TRY (drule expand_dec) >> simp [])
  >- (simp [AllCaseEqs ()] >> rw[effect_def] >> (drule expand_dec) >> simp [])
  >- (simp [AllCaseEqs ()] >> rw[effect_def,resulting_def] >> TRY (drule expand_dec) >> simp [])
  >- (simp [AllCaseEqs ()] >> rw[effect_def,resulting_def] >> TRY (drule expand_dec) >> simp[wasmSemanticPrimitivesTheory.ainstr_size_def,pairTheory.LEX_DEF])
)

val evaluate_wasm_def = tDefine "evaluate_wasm" `
  evaluate_wasm s = case s.code of
    | vs, [] => (wrap_result vs, s)
    | vs, es => case evaluate_small s of
      | SOME r', s' => (r', s')
      | NONE   , s' => evaluate_wasm s'
`
(
  WF_REL_TAC `inv_image ($< LEX $<) (\s. (s.clock, ainstr2_size (SND s.code)))` >> rw [] >> drule evaluate_small_progress >> simp[wasmSemanticPrimitivesTheory.ainstr_size_def,pairTheory.LEX_DEF]
)

(* val evaluate_fill_b = Q.store_thm("evaluate_fill_b", *)
(*   `(s.code = ([], Label (LENGTH vs) is (fill_b l holed (vs, [Plain (Br (n2w l))])))) ==> ((SOME vs, s') = evaluate_wasm s)`, *)
(*   cheat *)
(* ) *)

(* val evaluate_fill_e = Q.store_thm("evaluate_fill_e", *)
(*   `(s.code = ([], Frame (LENGTH vs) f (fill_e holed (vs, [Plain Return])))) ==> ((SOME vs, s') = evaluate_wasm s)`, *)
(*   cheat *)
(* ) *)

(* TODO: Do we need something like evaluate_expression? *)

val _ = export_theory()
