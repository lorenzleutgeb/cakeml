open preamble exhSemTheory;

val _ = new_theory"exhProps";

val build_rec_env_merge = store_thm("build_rec_env_merge",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[] >>
  PairCases_on`h` >> rw[])

val Boolv_disjoint = save_thm("Boolv_disjoint",EVAL``exhSem$Boolv T = Boolv F``);

val pmatch_any_match = store_thm("pmatch_any_match",
  ``(∀s p v env env'. pmatch s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_no_match = store_thm("pmatch_any_no_match",
  ``(∀s p v env. pmatch s p v env = No_match ⇒
       ∀env. pmatch s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list s ps vs env = No_match ⇒
       ∀env. pmatch_list s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  imp_res_tac pmatch_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_any_match_error = store_thm("pmatch_any_match_error",
  ``(∀s p v env. pmatch s p v env = Match_type_error ⇒
       ∀env. pmatch s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list s ps vs env = Match_type_error)``,
  rw[] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_any_no_match,pmatch_any_match]);

val pmatch_list_pairwise = store_thm("pmatch_list_pairwise",
  ``∀ps vs s env env'. pmatch_list s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_any_match])

val _ = store_thm("pmatch_list_snoc_nil[simp]",
  ``∀p ps v vs s env.
      (pmatch_list s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list s (SNOC p ps) [] env = Match_type_error)``,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_def]);

val pmatch_list_snoc = store_thm("pmatch_list_snoc",
  ``∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list s ps vs env of
      | Match env' => pmatch s p v env'
      | res => res``,
  Induct >> Cases_on`vs` >> simp[pmatch_def] >> rw[] >>
  BasicProvers.CASE_TAC)

val pmatch_append = store_thm("pmatch_append",
  ``(∀s p v env n.
      (pmatch s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch s p v (TAKE n env)))) ∧
    (∀s ps vs env n.
      (pmatch_list s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list s ps vs (TAKE n env))))``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def]
  >- ( BasicProvers.CASE_TAC >> fs[] >>
       BasicProvers.CASE_TAC >> fs[]) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch s p v (TAKE n env)`>>fs[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch s p v (TAKE n env) = Match env1` >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND] )

val pmatch_nil = save_thm("pmatch_nil",
  LIST_CONJ [
    pmatch_append
    |> CONJUNCT1
    |> Q.SPECL[`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_append
    |> CONJUNCT2
    |> Q.SPECL[`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val _ = export_theory()
