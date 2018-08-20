(* NOTE: Please consult README.md *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmLangTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmStatic"

(* 3  Validation *)
(* 3.1.1  Contexts *)
val _ = Datatype `context =
  <| types:   functype   list
   ; funcs:   functype   list
   ; tables:  tabletype  list
   ; mems:    memtype    list
   ; globals: globaltype list
   ; locals:  valtype    list
   ; labels:  resulttype list
   ; return:  resulttype option
   |>`

(* 3.2  Types *)
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
val limit_ok_def = Define `limit_ok l = case l.max of NONE => T | SOME m => (w2n m) <= (w2n l.min)`

(* 3.2.2  Function Types *)
val functype_ok_def = Define `functype_ok (t1s _> t2s) = ((LENGTH t2s) < 1n)`

(* 3.2.3  Table Types *)
val tabletype_ok_def = Define `tabletype_ok (T_table ls elt) = limit_ok ls`

(* 3.2.4 Memory Types *)
val memtype_ok_def = Define `memtype_ok = limit_ok`

(* (* 3.2.5  Global Types *) *)
val globaltype_ok_def = Define `globaltype_ok g = T`

(* 3.3  Instructions *)

(* Shorthands for common function types. *)
val endofunc_def = Define `endofunc = W Tf`
val consumes_def = Define `consumes t = Tf t []` (* C combinator not found? *)
val produces_def = Define `produces = Tf []`

(* Helper mostly used to check something is defined correctly in the context. *)
val has_def = Define `has xs i x = (i < (LENGTH xs) /\ EL i xs = x)`

(* Helper that takes a context and prepends a label to its labels. *)
val labelled_def = Define `labelled c l = (c with labels := (l :: c.labels))`

(* Helper to check well-formedness of Memory Instructions. *)
val align_ok_def = Define `align_ok ma n = (2 EXP (w2n ma.align) <= n DIV 8)`

(* Helper to check whether a context has some defined memory. *)
val hasmem_def = Define `hasmem c = (c.mems <> [])`

(* NOTE: Typing of Instructions is combined with typing of Instruction Sequences. *)
val (typ_rules, typ_cases, typ_ind) = Hol_reln `
(* 3.3.1.1 *)
(! c v . c |- [Const v] ::- ([] _> [(typeof v)])) /\
(* 3.3.1.2 - 3.3.1.5 *)
(! c t p . t = Tv Ki w ==> c |- [Unop_i w p] ::- endofunc [t]) /\
(! c t p . t = Tv Kf w ==> c |- [Unop_f w p] ::- endofunc [t]) /\
(! c t p . t = Tv Ki w ==> c |- [Binop_i w p] ::- ([t; t] _> [t])) /\
(! c t p . t = Tv Kf w ==> c |- [Binop_f w p] ::- ([t; t] _> [t])) /\
(! c t p . t = Tv Ki w ==> c |- [Testop_i w p] ::- ([t] _> [T_i32])) /\
(! c t p . t = Tv Ki w ==> c |- [Relop_i w p] ::- ([t; t] _> [T_i32])) /\
(! c t p . t = Tv Kf w ==> c |- [Relop_f w p] ::- ([t; t] _> [T_i32])) /\
(* 3.3.1.6 *)
(! c. (c |- [Conversion Wrap] ::- ([T_i64] _> [T_i32]))) /\
(! c sx. (c |- [Conversion (Extend sx)] ::- ([T_i32] _> [T_i64]))) /\
(! c w1 w2 sx. (c |- [Conversion (Trunc t1 sx t2)] ::- ([Tv Kf w2] _> [Tv Ki w1]))) /\
(! c. (c |- [Conversion Demote] ::- ([T_f64] _> [T_f32]))) /\
(! c. (c |- [Conversion Promote] ::- ([T_f32] _> [T_f64]))) /\
(! c w1 w2 sx. (c |- [Conversion (Convert w1 sx w2)] ::- ([Tv Ki w2] _> [Tv Ki w1]))) /\
(! c t . (c |- [Conversion (Reinterpret t)] ::- ([other_kind t] _> [t]))) /\
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
(! c t . (hasmem c /\ (align_ok ma (bit_width t))) ==> c |- [Load t NONE ma] ::- [T_i32] _> [t]) /\
(! c t tp . (hasmem c /\ (align_ok ma (bit_width_p tp)) /\ (FST arg) = tp) ==> c |- [Load t (SOME arg) ma] ::- [T_i32] _> [t]) /\
(* 3.3.4.3 - 3.3.4.4 *)
(! c t . (hasmem c /\ (align_ok ma (bit_width t))) ==> c |- [Store t NONE ma] ::- consumes [T_i32; t]) /\
(! c t tp . (hasmem c /\ (align_ok ma (bit_width_p tp))) ==> c |- [Store t (SOME tp) ma] ::- consumes [T_i32; t]) /\
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

val is_const_expr_def = Define `is_const_expr c (Expr is) = (EVERY (is_const_instr c) is)`

(* 3.4  Modules *)

(* 3.4.1.1 *)
val typ_func_def = Define `(! c f t . typ_func c f t = ? t1s t2s . ((has c.types (w2n f.type) t) /\ (t = t1s _> t2s) /\ (typ_expr (c with <| locals := t1s ++ f.locals; labels := [t2s]; return := SOME t2s |>) f.body t2s)))`

(* 3.4.2.1 *)
val typ_table_def = Define `typ_table (t:table) ty <=> tabletype_ok t.type /\ t.type = ty`

(* 3.4.3.1 *)
val typ_mem_def = Define `typ_mem (m:mem) ty <=> memtype_ok m.type /\ m.type = ty`

(* 3.4.4.1 *)
val typ_global_def = Define `typ_global c (g:global) ty <=> ? mut t . ty = T_global mut t /\ (globaltype_ok g.type /\ typ_expr c g.init [t] /\ is_const_expr c g.init) /\ g.type = ty`

(* 3.4.5.1 *)
val elem_ok_def = Define `elem_ok c e = ? ls . (has c.tables (w2n e.table) (T_table ls T_anyfunc) /\ typ_expr c e.offset [T_i32] /\ is_const_expr c e.offset /\ (EVERY (\x . (?t' . has c.funcs (w2n x) t')) e.init))`

(* 3.4.6.1 *)
val data_ok_def = Define `data_ok c d = ? m . has c.mems (w2n d.data) m /\ typ_expr c d.offset [T_i32] /\ is_const_expr c d.offset`

(* 3.4.7.1 *)
val start_ok_def = Define `(! c s . (start_ok c s) <=> (has c.funcs (w2n s.func) (endofunc [])))`

(* 3.4.8.2 - 3.4.8.5 *)
val typ_exportdesc_def = Define `
(typ_exportdesc c (Export_func x) (Te_func t) <=> (has c.funcs (w2n x) t)) /\
(typ_exportdesc c (Export_table x) (Te_table t) <=> (has c.tables (w2n x) t)) /\
(typ_exportdesc c (Export_mem x) (Te_mem t) <=> (has c.mems (w2n x) t)) /\
(typ_exportdesc c (Export_global x) (Te_global t) <=> (has c.globals (w2n x) t /\ ~is_var t))
`

val guess_typ_exportdesc_def = Define `
(guess_typ_exportdesc (m:module) (Export_func x) = (Te_func (EL (w2n x) m.types))) /\
(guess_typ_exportdesc (m:module) (Export_table x) = (Te_table (EL (w2n x) m.tables).type)) /\
(guess_typ_exportdesc (m:module) (Export_mem x) = (Te_mem (EL (w2n x) m.mems).type)) /\
(guess_typ_exportdesc (m:module) (Export_global x) = (Te_global (EL (w2n x) m.globals).type))
`

(* 3.4.8.1 *)
val typ_export_def = Define `typ_export c e t = typ_exportdesc c e.desc t`
val guess_typ_export_def = Define `guess_typ_export m e = guess_typ_exportdesc m e.desc`

(* 3.4.9.2 - 3.4.9.5 *)
val typ_importdesc_def = Define `
(typ_importdesc c (Import_func x) (Te_func t) <=> (has c.types (w2n x) t)) /\
(typ_importdesc c (Import_table t) ty <=> (tabletype_ok t /\ ty = Te_table t)) /\
(typ_importdesc c (Import_mem t) ty <=> (memtype_ok t /\ ty = Te_mem t)) /\
(typ_importdesc c (Import_global t) ty <=> (globaltype_ok t /\ ~is_var t /\ ty = Te_global t))
`

val guess_typ_importdesc = Define `
(guess_typ_importdesc m (Import_func x) = Te_func (EL (w2n x) (m:module).types)) /\
(guess_typ_importdesc m (Import_table t) = Te_table t) /\
(guess_typ_importdesc m (Import_mem t) = Te_mem t) /\
(guess_typ_importdesc m (Import_global t) = Te_global t)
`

(* 3.4.9.1 *)
val typ_import_def = Define `typ_import c i t = typ_importdesc c i.desc t`
val guess_typ_import_def = Define `guess_typ_import m i = guess_typ_importdesc m i.desc`

(* 3.4.10  Modules *)
val guess_typ_module_imports_def = Define `guess_typ_module_imports m = MAP (guess_typ_import m) m.imports`
val guess_typ_module_exports_def = Define `guess_typ_module_exports m = MAP (guess_typ_export m) m.exports`

val module_context_def = Define `
module_context m = let its = guess_typ_module_imports m in
  <| types   := m.types
   ; funcs   := (ext_funcs   its) ++ m.types
   ; tables  := (ext_tables  its) ++ (MAP (\x. x.type) m.tables)
   ; mems    := (ext_mems    its) ++ (MAP (\x. x.type) m.mems)
   ; globals := (ext_globals its) ++ (MAP (\x. x.type) m.globals)
   ; locals  := []
   ; labels  := []
   ; return  := NONE
   |>`

val typ_module_def = Define `
typ_module m its ets = (
let
  its = guess_typ_module_imports m;
  ets = guess_typ_module_exports m;
  c = module_context m;
  c' =
     <| types   := []
      ; funcs   := []
      ; tables  := []
      ; mems    := []
      ; globals := (ext_globals its)
      ; locals  := []
      ; labels  := []
      ; return  := NONE
      |>
in
  (EVERY functype_ok m.types) /\
  (EVERY (\x. ?t. typ_func c x t) m.funcs) /\
  (EVERY (\x. ?t. typ_table x t) m.tables) /\
  (EVERY (\x. ?t. typ_mem x t) m.mems) /\
  (EVERY (\x. ?t. typ_global c' x t) m.globals) /\
  (EVERY (\x. elem_ok c x) m.elem) /\
  (EVERY (\x. data_ok c x) m.data) /\
  ((OPTION_MAP (start_ok c) m.start) <> SOME F) /\
  (LENGTH c.tables <= 1) /\
  (LENGTH c.mems <= 1) /\
  (ALL_DISTINCT (MAP (\ (e:export). e.name) m.exports))
)`

val _ = export_theory ()
