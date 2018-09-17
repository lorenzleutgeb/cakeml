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

val _ = overload_on("state_empty", ``
  <| ffi  : []
   ; store: []
   ; frame: []
   ; code : []
   ; clock: []
   |>`
``)

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

val check_args_def = Define `types_match ts vs = LIST_REL (\t v. t = typeof v)`

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

(* TODO: Do we need something like evaluate_expression? *)

(* 4.5.3  Allocation *)

(* 4.5.3.1  Functions *)
val allocfunc_def = Define `
  allocfunc store func moduleinst =
    let funcaddr = LENGTH store.funcs in
    let functype = EL (w2n func.type) moduleinst.types in
    let funcinst = Native functype module func in
    (store with funcs := store.funcs ++ [funcinst], funcaddr)
`

(* 4.5.3.2  Host Functions *)
(* Currently, FFIs are the only host functions that can be allocated. *)
val allochostfunc_foreignfunction_def = Define `
  allochostfunc store ffi_name =
    let funcaddr = LENGTH store.funcs in
    let funcinst = Host (ForeignFunction ffi_name) in
    (store with funcs := store.funcs ++ [funcinst], funcaddr)
`

val LIST_MUL = Define `LIST_MUL l n = FUNPOW (APPEND l) n []`
val LIST_FILL = Define `LIST_FILL x n = LIST_MUL [x] n`

(* 4.5.3.3  Tables *)
val alloctable_def = Define `
  alloctable store (T_table tabletype elemtype) =
    let tableaddr = LENGTH store.tables in
    let tableinst =  <| elem: LIST_FILL NONE tabletype.min; max: tabletype.max |> in
    (store with tables := store.tables ++ [tableinst], tableaddr)
`

(* 4.5.3.4  Memories *)
val allocmem_def = Define `
  allocmem store memtype =
    let memaddr = LENGTH store.mems in
    let meminst = <| data: LIST_FILL 0w (memtype.min * page_size); memtype.max |> in
    (store with mems := store.mems ++ [meminst], memaddr)

(* 4.5.3.5  Globals *)
val allocglobal_def = Define `
  allocglobal store globbaltype (T_global mut valtype) =
    let globaladdr = LENGTH store.globals in
    let globalinst = <| value := v; mut := mut |> in
    (store with globals := store.globals ++ [globalinst])
`

(* 4.5.3.6  Growing Tables *)
val grow_ok_def = Define `
  growtable_ok tableinst n = case tableinst.max of
    | SOME m => if LENGTH tableinst.elem + n < tableinst.max then SOME n else NONE
    | NONE   => SOME n
`

val growtable_def = Define `
  growtable tableinst n = OPTION_MAP
    (\n. tableinst with elem := tableinst.elem ++ LIST_FILL NONE n)
    (growtable_ok tableinst n)
`

(* 4.5.3.7  Growing Memories *)
val growmem_ok_def = Define `
  growmem_ok meminst n = case meminst.data of
    | SOME m => if LENGTH meminst.data + n * page_size <= meminst.max * page_size then SOME n else NONE
    | NONE   => SOME n
`

val growmem_def = Define `
  growmem meminst n = OPTION_MAP
    (\n. meminst with data := meminst.data ++ LIST_FILL 0w (n * page_size))
    (growtable_ok meminst n)
`

(* 4.5.3.8  Modules *)
val allocx_def = Define `
  allocx (f:store -> 'a -> (store, idx)) store (xs:'a list) = FOLDR
    (\x. (s, idxs). val (s', idx) = f s x in (s', idx::idxs))
    (store, [])
    xs
`

val moduleinst_from_imports_def = Define `
  moduleinst_from_imports module imports =
    <| types       := module.types
     ; funcaddrs   := externval_funcs   externalvals
     ; tableaddrs  := externval_tables  imports
     ; memaddrs    := externval_mems    imports
     ; globaladdrs := externval_globals imports
     |>`

val create_export_def = Define `
  create_export moduleinst export = case export.desc of
  | Export_func   idx => Func   (EL (w2n idx) meminst.funcs)
  | Export_table  idx => Table  (EL (w2n idx) meminst.tables)
  | Export_mem    idx => Mem    (EL (w2n idx) meminst.mems)
  | Export_global idx => Global (EL (w2n idx) meminst.globals)
`

val allocmodule_def = Define `
  allocmodule store module externalvals vs =
    let moduleinst = moduleinst_from_imports module externalvals in
    let (s1, funcaddrs) = allocx allocfunc s (MAP (\x. (x, moduleinst)) module.funcs) in
    let (s2, tableaddrs) = allocx alloctable s1 (MAP (\x. x.type) module.tables) in
    let (s3, memaddrs) = allocx allocmem s2 (MAP (\x. x.type) module.mems) in
    let (s', globaladdrs) = allocx allocglobal s3 (MAP (\x. x.type) module.globals) in
    let moduleinst = moduleinst with
      <|   funcaddrs := moduleinst.funcaddrs   ++ [  funcaddrs]
       ;  tableaddrs := moduleinst.tableaddrs  ++ [ tableaddrs]
       ;    memaddrs := moduleinst.tableaddrs  ++ [ tableaddrs]
       ; globaladdrs := moduleinst.globaladdrs ++ [globaladdrs]
       |>
    let moduleinst = moduleinst with exports := MAP (create_export moduleinst) module.exports in
      (s', moduleinst)
`

(* 4.5.5  Invocation *)
val _ = Datatype `invocation_result = Success (result # 'ffi state) | Failure`

val invoke_def = Define `
  invoke ffi clock store a vs =
    if LENGTH store.funcs < a then Failure else
    let Tf args b = (EL a store.funcs).type in
    if ~(check_args args vs) then Failure else
      Success (evaluate_wasm
        <| code  := (vs, [Invoke a])
         ; clock := clock
         ; store := store
         ; frame := frame_empty
         ; ffi   := ffi
         |>
       )`

val invoke_from_def = Define `invoke_from s = invoke s.ffi s.clock s.store`

(* Turns imports that refer to FFI in external values that represent their implementation. *)
val stub_ffi_def = Define `
  stub_ffi module import = if import.module <> (string_to_name "ffi") then NONE else case import.desc of
  | Import_func typeidx => SOME <| module  |>
  | _ => NONE
`

val stub_imports_def = Define `
  stub_ffi module = MAP (module.imports)
`

(* 4.5.4  Instantiation *)
val instantiate_def = Define `
  instantiate ffi clock imports module = state_empty
    (* let moduleinst_im = moduleinst_empty with globaladdrs := externval_globals imports in *)
    (* let f_im = frame_empty with module := moduleinst_im in *)
    (* let globvals = MAP wasm_evaluate (\g. <| code := ([], [Frame 0 ([], expr_to_instrs g.expr)]); ffi := ffi; clock := clock |>) module.globals in *)
`

val instantiate_with_stubbed_ffi = Define `
  instantiate_with_stubbed_ffi ffi clock module = instantiate ffi clock (stub_imports module.imports) module
`

(* TODO: Observational Semantics *)

val _ = export_theory()
