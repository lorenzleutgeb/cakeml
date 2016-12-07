(*Generated by Lem from evaluate.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasives_extraTheory libTheory astTheory ffiTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();



val _ = new_theory "evaluate"

(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ast*)
(*open import SemanticPrimitives*)
(*open import Ffi*)

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

val _ = Define `
 (fix_clock s (s',res)= 
  (( s' with<| clock := (if s'.clock <= s.clock
                     then s'.clock else s.clock) |>),res))`;


val _ = Define `
 (dec_clock s=  (( s with<| clock := (s.clock -( 1 : num)) |>)))`;


(* list_result is equivalent to map_result (\v. [v]) I, where map_result is
 * defined in evalPropsTheory *)
 val _ = Define `

(list_result (Rval v)=  (Rval [v]))
/\
(list_result (Rerr e)=  (Rerr e))`;


(*val evaluate : forall 'ffi. state 'ffi -> environment v -> list exp -> state 'ffi * result (list v) v*)
(*val evaluate_match : forall 'ffi. state 'ffi -> environment v -> v -> list (pat * exp) -> v -> state 'ffi * result (list v) v*)
 val evaluate_defn = Defn.Hol_multi_defns `

(evaluate st env []=  (st, Rval []))
/\
(evaluate st env (e1::e2::es)=  
 ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case evaluate st' env (e2::es) of
        (st'', Rval vs) => (st'', Rval (HD v1::vs))
      | res => res
      )
  | res => res
  )))
/\
(evaluate st env [Lit l]=  (st, Rval [Litv l]))
/\
(evaluate st env [Raise e]=  
 ((case evaluate st env [e] of
    (st', Rval v) => (st', Rerr (Rraise (HD v)))
  | res => res
  )))
/\
(evaluate st env [Handle e pes]=  
 ((case fix_clock st (evaluate st env [e]) of
    (st', Rerr (Rraise v)) => evaluate_match st' env v pes v
  | res => res
  )))
/\
(evaluate st env [Con cn es]=  
 (if do_con_check env.c cn (LENGTH es) then
    (case evaluate st env (REVERSE es) of
      (st', Rval vs) =>
        (case build_conv env.c cn (REVERSE vs) of
          SOME v => (st', Rval [v])
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
    | res => res
    )
  else (st, Rerr (Rabort Rtype_error))))
/\
(evaluate st env [Var n]=  
 ((case lookup_var_id n env of
    SOME v => (st, Rval [v])
  | NONE => (st, Rerr (Rabort Rtype_error))
  )))
/\
(evaluate st env [Fun x e]=  (st, Rval [Closure env x e]))
/\
(evaluate st env [App op es]=  
 ((case fix_clock st (evaluate st env (REVERSE es)) of
    (st', Rval vs) =>
      if op = Opapp then
        (case do_opapp (REVERSE vs) of
          SOME (env',e) =>
            if st'.clock =( 0 : num) then
              (st', Rerr (Rabort Rtimeout_error))
            else
              evaluate (dec_clock st') env' [e]
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
      else
        (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
          SOME ((refs,ffi),r) => (( st' with<| refs := refs; ffi := ffi |>), list_result r)
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
  | res => res
  )))
/\
(evaluate st env [Log lop e1 e2]=  
 ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case do_log lop (HD v1) e2 of
        SOME (Exp e) => evaluate st' env [e]
      | SOME (Val v) => (st', Rval [v])
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
(evaluate st env [If e1 e2 e3]=  
 ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) =>
      (case do_if (HD v) e2 e3 of
        SOME e => evaluate st' env [e]
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
(evaluate st env [Mat e pes]=  
 ((case fix_clock st (evaluate st env [e]) of
    (st', Rval v) =>
      evaluate_match st' env (HD v) pes Bindv
  | res => res
  )))
/\
(evaluate st env [Let xo e1 e2]=  
 ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) => evaluate st' ( env with<| v := (opt_bind xo (HD v) env.v) |>) [e2]
  | res => res
  )))
/\
(evaluate st env [Letrec funs e]=  
 (if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
    evaluate st ( env with<| v := (build_rec_env funs env env.v) |>) [e]
  else
    (st, Rerr (Rabort Rtype_error))))
/\
(evaluate st env [Tannot e t]=  
 (evaluate st env [e]))
/\
(evaluate_match st env v [] err_v=  (st, Rerr (Rraise err_v)))
/\
(evaluate_match st env v ((p,e)::pes) err_v=  
  (if ALL_DISTINCT (pat_bindings p []) then
    (case pmatch env.c st.refs p v env.v of
      Match env_v' => evaluate st ( env with<| v := env_v' |>) [e]
    | No_match => evaluate_match st env v pes err_v
    | Match_type_error => (st, Rerr (Rabort Rtype_error))
    )
  else (st, Rerr (Rabort Rtype_error))))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) evaluate_defn;

(*val evaluate_decs : forall 'ffi. maybe modN -> state 'ffi -> environment v -> list dec -> state 'ffi * flat_env_ctor * result env_val v*)
 val _ = Define `

(evaluate_decs mn st env []=  (st, [], Rval []))
/\
(evaluate_decs mn st env (d1::d2::ds)=  
 ((case evaluate_decs mn st env [d1] of
    (st, new_ctors, Rval new_vals) =>
      (case
        evaluate_decs mn st (extend_dec_env new_vals new_ctors env) (d2::ds)
      of (st',new_ctors',r) =>
        (st', (new_ctors'++new_ctors), combine_dec_result new_vals r)
      )
  | res => res
  )))
/\
(evaluate_decs mn st env [Dlet p e]=  
 (if ALL_DISTINCT (pat_bindings p []) then
    (case evaluate st env [e] of
      (st', Rval v) =>
        (st',
         [],
         (case pmatch env.c st'.refs p (HD v) [] of
           Match new_vals => Rval new_vals
         | No_match => Rerr (Rraise Bindv)
         | Match_type_error => Rerr (Rabort Rtype_error)
         ))
    | (st', Rerr err) => (st', [], Rerr err)
    )
  else
    (st, [], Rerr (Rabort Rtype_error))))
/\
(evaluate_decs mn st env [Dletrec funs]= 
  (st,
   [],   
(if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
     Rval (build_rec_env funs env [])
   else
     Rerr (Rabort Rtype_error))))
/\
(evaluate_decs mn st env [Dtype tds]=  
 (let new_tdecs = (type_defs_to_new_tdecs mn tds) in
    if check_dup_ctors tds /\
       DISJOINT new_tdecs st.defined_types /\
       ALL_DISTINCT (MAP (\ (tvs,tn,ctors) .  tn) tds)
    then
      (( st with<| defined_types := (new_tdecs UNION st.defined_types) |>), build_tdefs mn tds, Rval [])
    else
      (st, [], Rerr (Rabort Rtype_error))))
/\
(evaluate_decs mn st env [Dtabbrev tvs tn t]= 
  (st, [], Rval []))
/\
(evaluate_decs mn st env [Dexn cn ts]=  
 (if TypeExn (mk_id mn cn) IN st.defined_types then
    (st, [], Rerr (Rabort Rtype_error))
  else
    (( st with<| defined_types := ({TypeExn (mk_id mn cn)} UNION st.defined_types) |>),
     [(cn, (LENGTH ts, TypeExn (mk_id mn cn)))],
     Rval [])))`;


(*val evaluate_tops : forall 'ffi. state 'ffi -> environment v -> list top -> state 'ffi * env_ctor * result (env_mod * env_val) v*)
 val _ = Define `

(evaluate_tops st env []=  (st, ([],[]), Rval ([],[])))
/\
(evaluate_tops st env (top1::top2::tops)=  
 ((case evaluate_tops st env [top1] of
    (st', new_ctors, Rval (new_mods,new_vals)) =>
      (case evaluate_tops st' (extend_top_env new_mods new_vals new_ctors env) (top2::tops) of
        (st'', new_ctors', r) =>
        (st'',
         merge_alist_mod_env new_ctors' new_ctors,
         combine_mod_result new_mods new_vals r)
      )
  | res => res
  )))
/\
(evaluate_tops st env [Tdec d]=  
 ((case evaluate_decs NONE st env [d] of
    (st', new_ctors, Rval new_vals) =>
      (st', ([],new_ctors), Rval ([],new_vals))
  | (st', new_ctors, Rerr err) =>
      (st', ([],[]), Rerr err)
  )))
/\
(evaluate_tops st env [Tmod mn specs ds]=  
 (if ~ (mn IN st.defined_mods) /\ no_dup_types ds
  then
    (case evaluate_decs (SOME mn) st env ds of
      (st', new_ctors, r) =>
        (( st' with<| defined_mods := ({mn} UNION st'.defined_mods) |>),
         ([(mn,new_ctors)],[]),
         (case r of
           Rval new_vals => Rval ([(mn,new_vals)],[])
         | Rerr err => Rerr err
         ))
    )
  else
    (st, ([],[]), Rerr (Rabort Rtype_error))))`;


(*val evaluate_prog : forall 'ffi. state 'ffi -> environment v -> prog -> state 'ffi * env_ctor * result (env_mod * env_val) v*)
val _ = Define `

(evaluate_prog st env prog=  
 (if no_dup_mods prog st.defined_mods /\ no_dup_top_types prog st.defined_types then
    evaluate_tops st env prog
  else
    (st, ([],[]), Rerr (Rabort Rtype_error))))`;

val _ = export_theory()

