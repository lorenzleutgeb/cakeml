open preamble wasmSemTheory wasmRelSemTheory

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()
val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmBoth"

val state_rel_def = Define `
  state_rel rs fs =
    rs.ffi   = fs.ffi   /\
    rs.store = fs.store /\
    rs.frame = fs.frame /\
    rs.code  = fs.code`

val to_small_state_def = Define `
  to_small_state (s:wasmSem$state) = (
    <| ffi:    s.ffi
     ; store:  s.store
     ; frame:  s.frame
     ; code:   s.code
     ; result: NONE
     |>
    ):wasmRelSem$state`

val to_small_state_rel = Q.store_thm("to_small_state_rel",
  `(∀s. state_rel (to_small_state s) s)`,
  cheat
)

val small_to_big = Q.store_thm("small_to_big",
  `(∀r s s'.
      (evaluate s = (r, s') ∧ r ≠ Timeout)
    ⇒
      (∃x. (to_small_state s) --->* x ∧ state_rel x s' ∧ x.result = (SOME r))
   )`,
  cheat
)

val _ = export_theory()
