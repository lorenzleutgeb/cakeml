open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmSemTheory patternMatchesLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSem"

val spop_def = Define `spop s = s with stack := TL s.stack`
val spush_def = Define `spush i s = s with stack := i :: s.stack`
val stack_only_def = Define `stack_only s is = (NONE, s with stack := is)`
val stack_and_fuel_def = Define `stack_and_fuel s is = if s.clock = 0 then (SOME Timeout, s) else (NONE, s with stack := is ; clock := (s.clock - 1))`
val typ_assert = Define `typ_assert bs s = if b then (NONE, s) else (SOME TypeError, s)`

val _ = Datatype `
  result =
    | TypeError string
    | Timeout`

val evaluate_small_def = Define `
  evaluate_small s = case s.stack of
    | Trap :: t =>
      stack_only s [Trap]
    (* 4.4.1.2 *)
    | (Unop_i W32 op) :: ci32 c :: t =>
      stack_only s ((ci32 (app_unop_i op c)) :: t)
    | (Unop_i W64 op) :: ci64 c :: t =>
      stack_only s ((ci64 (app_unop_i op c)) :: t)
    | (Unop_f W32 op) :: Const (V_f32 c) :: t =>
      stack_only s ((cf32 (app_unop_f op c)) :: t)
    | (Unop_f W64 op) :: Const (V_f64 c) :: t =>
      stack_only s ((cf64 (app_unop_f op c)) :: t)
    (* 4.4.1.3 *)
    | (Binop_i W32 op) :: ci32 c1 :: ci32 c2 :: t =>
      stack_only s ((wrap_option V_i32 (app_binop_i op c1 c2)) :: t)
    | (Binop_i W64 op) :: ci64 c1 :: ci64 c2 :: t =>
      stack_only s ((wrap_option V_i64 (app_binop_i op c1 c2)) :: t)
    | (Binop_f W32 op) :: cf32 c1 :: cf32 c2 :: t =>
      stack_only s ((wrap_option V_f32 (app_binop_f op c1 c2)) :: t)
    | (Binop_f W64 op) :: cf64 c1 :: cf64 c2 :: t =>
      stack_only s ((wrap_option V_f64 (app_binop_f op c1 c2)) :: t)
    (* 4.4.1.4 *)
    | (Testop_i W32 op) :: ci32 c :: t =>
      stack_only s ((wrap_bool (app_testop_i op c)) :: t)
    | (Testop_i W64 op) :: ci64 c :: t =>
      stack_only s ((wrap_bool (app_testop_i op c)) :: t)
    (* 4.4.1.5 *)
    | (Relop_i W32 op) :: ci32 c1 :: ci32 c2 :: t =>
      stack_only ((wrap_bool (app_relop_i op c1 c2)) :: t)
    | (Relop_i W64 op) :: ci64 c1 :: ci64 c2 :: t =>
      stack_only ((wrap_bool (app_relop_i op c1 c2)) :: t)
    | (Relop_f W32 op) :: cf32 c1 :: cf32 c2 :: t =>
      stack_only ((wrap_bool (app_relop_f op c1 c2)) :: t)
    | (Relop_f W64 op) :: cf64 c1 :: cf64 c2 :: t =>
      stack_only ((wrap_bool (app_relop_f op c1 c2)) :: t)
    (* 4.4.1.6 *)
    | (Conversion c) :: Const v :: t =>
      stack_only s ((wrap_option (\x.x) (cvt c v)) :: t)
    (* 4.4.2.1 *)
    | Drop :: Const v :: t =>
      stack_only s t
    (* 4.4.2.2 *)
    | Select :: (wrap_bool b) :: c1 :: c2 :: t =>
      stack_only s ((if b then c2 else c1) :: t)
    (* 4.4.3.3 *)
    | Tee_local x :: c :: t =>
      stack_and_fuel s (Set_local x :: c :: c :: t) (* Stack grows! *)
    (* 4.4.5.1 *)
    | Nop :: t =>
      stack_only s t
    (* 4.4.5.2 *)
    | Unreachable :: t =>
      stack_only s [Trap]
    (* 4.4.5.3 *)
    | Block t is :: t =>
      stack_and_fuel s ((Label (LENGTH t) [] is) :: t) (* Same height, block is swapped for label. *)
    (* 4.4.5.4 *)
    | Loop t is :: t =>
      stack_and_fuel s ((Label 0 [Loop t is] is) :: t) (* Same height, loop is swapped for label. *)
    (* 4.4.5.5 *)
    | If t i1s i2s :: wrap_bool v :: t =>
      stack_only s ((Label (LENGTH t) [] (if v then i1s else i2s)) :: t)
    (* 4.4.5.6 *)
    | Label n is (fill_b l holed (vs ++ [Br (n2w l)]) =>
      typ_assert
        [("4.4.5.6.4", n = (LENGTH vs) /\ EVERY is_val vs)]
        (stack_and_fuel s (vs ++ is ++ t)) (* Stack grows, since continuation is expanded! *)
    (* 4.4.5.7 *)
   | Br_if l :: wrap_bool v :: t =>
      stack_only s (if v then [Br l] else []) ++ t
    (* 4.4.5.8 *)
    | Br_table ls ln :: ci32 (n2w i) :: t =>
      stack_only s (if i < LENGTH ls then EL i ls else ln) :: t
    (* 4.4.6.2 *)
    | Label n is vs :: t =>
      typ_assert
        [("?", EVERY is_val vs)]
        (stack_and_fuel vs ++ t) (* Stack grows, since label is expanded! *)
    (* 4.4.3.1 *)
    | Get_local (n2w x) :: t =>
      typ_assert
        [("4.4.3.1.2", x < LENGTH s.frame.locals)]
        (stack_only s ((Const (EL x s.frame.locals)) :: t))
    (* 4.4.3.2 *)
    | Set_local (n2w x) :: Const v :: t =>
      typ_assert
        [("4.4.3.2.2", x < LENGTH s.frame.locals)]
        (s with frame := (s.frame with locals := LUPDATE v x s.frame.locals); stack := t)
    (* 4.4.3.4 *)
    | Get_global (n2w x) :: t =>
      if LENGTH s.frame.module.globaladdrs >= x then
        (SOME TypeError "4.4.3.4.2", s)
      else
        let a = EL x s.frame.module.globaladdrs in
          if LENGTH s.store.globals <= a then
              (SOME TypeError "4.4.3.4.4", s)
          else
              stack_only s (Const (EL a s.globals).value)
    | Set_global (n2w x) :: Const v =>
      if LENGTH s.frame.module.globaladdrs >= x then
          (SOME TypeError "4.4.3.5.2", s)
      else
          let a = EL x s.frame.module.globaladdrs in
              if LENGTH s.store.globals <= a then
                  (SOME TypeError "4.4.3.5.4")
          in
          end

    | _ => (SOME TypeError "No reduction rule applicable; stack does not match.", s)
`

val evaluate_def = Define `
  evaluate s = case (s.result, s.stack) of
    | (vs, [])        => (Result s.result, s)
    | (vs, Trap :: t) => (Error, s)
    | (vs, is)        => case evaluate_small s of
      | (SOME r, s') => (r', s')
      | (NONE, s')   => evaluate s'`

val _ = export_theory()
