open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmSemTheory patternMatchesLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmFunctionalSem"

val spop_def = Define `spop 0 s = s /\ spop n s = spop (n - 1) (let h::t = s.stack in s with stack := t)`
val spush_def = Define `spush i s = s with stack := i :: s.stack`

val evaluate_def = Define `
  evaluate s = case s.stack of
    | Trap :: t =>
      (SOME 1, spop 1 s)
    | Drop :: Const v :: t =>
      (NONE, spop 2 s)
    | Get_local (n2w x) :: t =>
      (NONE, (spush (Const (EL x s.frame.locals)) (spop 1 s))
    | _ => (SOME 1, s)
`

val _ = export_theory()
