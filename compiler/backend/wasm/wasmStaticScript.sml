(* NOTE: Please consult README.md *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmLangTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmStatic";

(* 3  Validation *)
(* 3.1.1  Contexts *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#contexts%E2%91%A0 *)
val _ = Datatype `context = <|
  types:   functype   list;
  funcs:   functype   list;
  tables:  tabletype  list;
  mems:    memtype    list;
  globals: globaltype list;
  locals:  valtype    list;
  labels:  resulttype list;
  return:  resulttype option
|>`

(* 3.2  Types *)
(* Following operator shall correspond to the typing rule operator. *)
val _ = add_rule {
  fixity      = Infix(NONASSOC, 450),
  pp_elements = [
    HardSpace 1,
    TOK "|-",
    HardSpace 1,
    TM,
    HardSpace 1,
    TOK "::-",
    HardSpace 1
  ],
  term_name   = "typ",
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))
}
val _ = add_rule {
  fixity      = Infix(NONASSOC, 450),
  pp_elements = [
    HardSpace 1,
    TOK "⫢",
    HardSpace 1,
    TM,
    HardSpace 1,
    TOK "⫶",
    HardSpace 1
  ],
  term_name   = "typ",
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0))
}

(* 3.2  Types *)

(* 3.2.1  Limits*)
val typ_limit_def = Define `typ_limit l = case l.max of NONE => T | SOME m => (w2n m) <= (w2n l.min)`

(* 3.2.2  Function Types *)
val typ_functype_def = Define `typ_functype (t1s _> t2s) = ((LENGTH t2s) < 1n)`

(* 3.2.3  Table Types *)
val typ_tabletype_def = Define `typ_tabletype (T_table ls elt) = typ_limit ls`

(* 3.2.4 Memory Types *)
val typ_memtype_def = Define `typ_memtype = typ_limit`

(* 3.2.5  Global Types *)
val typ_globaltype_def = Define `typ_globaltype (g:globaltype) = T`

(* 3.3  Instructions *)

(* Shorthands for common function types. *)
val endofunc_def = Define `endofunc t = t _> t`
val consumes_def = Define `consumes t = t _> []`
val produces_def = Define `produces t = [] _> t`

(* Helper mostly used to check something is defined correctly in the context. *)
val has_def = Define `has xs i x = ((i < (LENGTH xs)) /\ ((EL i xs) = x))`

(* Helper that takes a context and prepends a label to its labels. *)
val labelled_def = Define `labelled c l = (c with labels := (l :: c.labels))`

(* Helper to check well-formedness of Memory Instructions. *)
val alignok_def = Define `alignok ma n =  ((2 EXP (w2n ma.align)) <= (n DIV 8))`

(* Helper to check whether a context has some defined memory. *)
val hasmem_def = Define `hasmem c = (c.mems <> [])`

(* NOTE: Typing of Instructions is combined with typing of Instruction Sequences. *)
val (typ_rules, typ_cases, typ_ind) = Hol_reln `
(* 3.3.1.1 *)
(! c v . c |- [Const v] ::- ([] _> [(typeof v)])) /\
(* 3.3.1.2 - 3.3.1.5 *)
(! c t p . is_int_t t ==> c |- [Unop_i t p] ::- endofunc [t]) /\
(! c t p . is_float_t t ==> c |- [Unop_f t p] ::- endofunc [t]) /\
(! c t p . is_int_t t ==> c |- [Binop_i t p] ::- ([t; t] _> [t])) /\
(! c t p . is_float_t t ==> c |- [Binop_f t p] ::- ([t; t] _> [t])) /\
(! c t p . is_int_t t ==> c |- [Testop_i t p] ::- ([t] _> [T_i32])) /\
(! c t p . is_int_t t ==> c |- [Relop_i t p] ::- ([t; t] _> [T_i32])) /\
(! c t p . is_float_t t ==> c |- [Relop_f t p] ::- ([t; t] _> [T_i32])) /\
(* 3.3.1.6 *)
(! c t1 t2 . (t1 <> t2 /\ ((is_float_t t1 /\ is_float_t t2) \/ (is_int_t t1 /\ is_int_t t2 /\ t_length t1 < t_length t2))) ==> (c |- [Cvtop t1 Convert t2 None] ::- ([t2] _> [t1]))) /\
(! c t1 t2 . (t1 <> t2 /\ t_length t1 = t_length t2) ==> c |- [Cvtop t1 Reinterpret t2 NONE] ::- ([t2] _> [t1])) /\
(* 3.3.2.1 - 3.3.2.2. *)
(! c t . c |- [Drop] ::- consumes [t]) /\
(! c t . c |- [Select] ::- [t; t; T_i32] _> [t]) /\
(* 3.3.3.1  - 3.3.3.5 *)
(! c t x . (has c.locals x t) ==> c |- [Get_local (n2w x)] ::- produces [t]) /\
(! c t x . (has c.locals x t) ==> c |- [Set_local (n2w x)] ::- consumes [t]) /\
(! c t x . (has c.locals x t) ==> c |- [Tee_local (n2w x)] ::- endofunc [t]) /\
(! c t x m . (has c.globals x (T_global m t)) ==> c |- [Get_global (n2w x)] ::- produces [t]) /\
(! c t x . (has c.globals x (T_global T_var t)) ==> c |- [Set_global (n2w x)] ::- consumes [t]) /\
(* 3.3.4.1 - 3.3.4.2 *)
(! c t . (hasmem c /\ (alignok ma (bit_width t))) ==> c |- [Load t NONE ma] ::- [T_i32] _> [t]) /\
(! c t tp . (hasmem c /\ (alignok ma (bit_width_p tp)) /\ (FST arg) = tp) ==> c |- [Load t (SOME arg) ma] ::- [T_i32] _> [t]) /\
(* 3.3.4.3 - 3.3.4.4 *)
(! c t . (hasmem c /\ (alignok ma (bit_width t))) ==> c |- [Store t NONE ma] ::- consumes [T_i32; t]) /\
(! c t tp . (hasmem c /\ (alignok ma (bit_width_p tp))) ==> c |- [Store t (SOME tp) ma] ::- consumes [T_i32; t]) /\
(* 3.3.4.5 - 3.3.4.6 *)
(! c . hasmem c ==> c |- [Current_memory] ::- produces [T_i32]) /\
(! c . hasmem c ==> c |- [Grow_memory] ::- endofunc [T_i32]) /\
(* 3.3.5.1 - 3.3.5.2 *)
(! c . c |- [Nop] ::- endofunc []) /\
(! c t1s t2s . c |- [Unreachable] ::- t1s _> t2s) /\
(* 3.3.5.3 - 3.3.5.5 *)
(! c ts is . (labelled c ts |- is ::- produces ts) ==> c |- [Block ts is] ::- produces ts) /\
(! c ts is . (labelled c ts |- is ::- produces ts) ==> c |- [Loop ts is] ::- produces ts) /\
(! c ts i1s i2s . ((((labelled c ts) |- i1s ::- produces ts) /\ ((labelled c ts) |- i2s ::- produces ts)) ==> c |- [If ts i1s i2s] ::- [T_i32] _> [t])) /\
(* 3.3.5.6 *)
(! c ts t1s t2s l . (has c.labels l ts) ==> c |- [Br (n2w l)] ::- (t1s ++ ts) _> t2s) /\
(* 3.3.5.7 *)
(! c ts l . (has c.labels l ts) ==> c |- [Br_if (n2w l)] ::- (ts ++ [T_i32]) _> ts) /\
(* 3.3.5.8 *)
(! c ts ln ls . (has c.labels ln ts /\ EVERY (\x . has c.labels x ts) ls) ==> c |- [Br_table (MAP n2w ls) (n2w ln)] ::- (ts ++ [T_i32]) _> ts) /\
(* 3.3.5.9 *)
(! c t t1s t2s . (c.return = (SOME t)) ==> c |- [Return] ::- (t1s ++ t) _> t2s) /\
(* 3.3.5.10 *)
(! c t x . (has c.funcs x t) ==> c |- [Call (n2w x)] ::- t) /\
(* 3.3.5.11 *)
(! c t1s t2s x ls . (has c.tables 0 (T_table ls T_anyfunc) /\ has c.types x (t1s _> t2s)) ==> c |- [Call_indirect (n2w x)] ::- (t1s ++ [T_i32]) _> t2s) /\
(* 3.3.6.1 *)
(! c ts . c |- [] ::- endofunc ts) /\
(* 3.3.6.2 *)
(! c t0s t1s t2s t3s ts i1s i2s . (t2s <> [] /\ t2s = (t0s ++ ts) /\ (c |- i1s ::- t1s _> (t0s ++ ts)) /\ (c |- i2s ::- ts _> t3s)) ==> (c |- (i1s ++ i2s) ::- t1s _> (t0s ++ t3s)))
`

(* 3.3.7.1 *)
val typ_expr_def = Define `(!c is ts . typ_expr c (Expr is) ts <=> (c |- is ::- [] _> ts))`

(* 3.3.7.2 *)
val is_const_instr_def = Define `is_const_instr c (Const cv) = T /\ is_const_instr c (Get_global x) = (?t . (has c.globals (w2n x) (T_global T_const t)))`
(* val isconst_def = Define `(! c i x t . i = (Const cv) \/ (i = (Get_global x) /\ (has c.globals (w2n x) (T_global T_const t))))` *)

val is_const_expr_def = Define `is_const_expr c (Expr is) = (EVERY (is_const_instr c) is)`


(* 3.4  Modules *)

(* 3.4.1.1 *)
val typ_func_def = Define `(! c f t . typ_func c f t = ? t1s t2s . ((has c.types (w2n f.type) t) /\ (t = t1s _> t2s) /\ (typ_expr (c with <| locals := t1s ++ f.locals; labels := [t2s]; return := SOME t2s |>) f.body t2s)))`

(* 3.4.2.1 *)
val typ_table_def = Define `typ_table (t:table) = typ_tabletype t.type`

(* 3.4.3.1 *)
val typ_mem_def = Define `typ_mem (m:mem) = typ_memtype m.type`

(* 3.4.4.1 *)
val typ_global_def = Define `typ_global c (g:global) t = (typ_globaltype g.type /\ typ_expr c g.init t /\ is_const_expr c g.init)`

(* 3.4.5.1 *)
val typ_elem_def = Define `typ_elem c e = ? ls . (has c.tables (w2n e.data) (T_table ls T_anyfunc) /\ typ_expr c e.offset [T_i32] /\ is_const_expr c e.offset /\ (EVERY (\x . (?t' . has c.funcs (w2n x) t')) e.init))`

(* 3.4.6.1 *)
val data_ok_def = Define `data_ok c d = ? m . has c.mems (w2n d.data) m /\ typ_expr c d.offset [T_i32] /\ is_const_expr c d.offset`

(* 3.4.7.1 *)
val start_ok_def = Define `(! c s . (start_ok c s) <=> (has c.funcs (w2n s.func) (endofunc [])))`

(* 3.4.8.1 *)
val exportdesc_typ_def = Define `
(exportdesc_typ c (Export_func x) (Te_func t) <=> (has c.funcs (w2n x) t)) /\
(exportdesc_typ c (Export_table x) (Te_table t) <=> (has c.tables (w2n x) t)) /\
(exportdesc_typ c (Export_mem x) (Te_mem t) <=> (has c.mems (w2n x) t)) /\
(exportdesc_typ c (Export_global x) (Te_global t) <=> (has c.globals (w2n x) t /\ ~is_var t))
`

(* 3.4.10  Modules *)
(* val module_typ_def = Define ` *)
(* module_typ ml *)

(* LENGTH c.tables <= 1 *)
(* LENGTH c.mems <= 1 *)
(*                      ets = *)
(* ets' =  *)
(* ` *)
