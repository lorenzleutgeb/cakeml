open preamble wasmSemTheory wasmRelSemTheory

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()
val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmBoth"

val states_agree_def = Define `
  states_agree (rs:'a wasmRelSem$state) (fs:'a wasmSem$state) <=>
    rs.ffi   = fs.ffi   /\
    rs.store = fs.store /\
    rs.frame = fs.frame /\
    rs.code  = fs.code`

val to_rel_state_def = Define `
  to_rel_state (s:'a wasmSem$state) =
    <| ffi    := s.ffi
     ; store  := s.store
     ; frame  := s.frame
     ; code   := s.code
     ; result := NONE
     |>`

val to_rel_state_agrees = Q.store_thm("to_rel_state_agrees",
  `∀s. states_agree (to_rel_state s) s`,
  rw[states_agree_def, to_rel_state_def]
)

val relsem_to_sem = Q.store_thm("relsem_to_sem",
  `(∀s s' r.
      (evaluate_wasm s = (r, s') ∧ r ≠ Timeout)
    <=>
      (∃x. (to_rel_state s) --->* x ∧ state_rel x s' ∧ x.result = (SOME r))
   )`,
  cheat
)

val _ = export_theory()
