open preamble
     stackSemTheory stackPropsTheory
     wasmStaticSemTheory
     wasmSemTheory

val _ = new_theory "stack_to_wasmProof"

(* TODO: Do we need correctness theorems for extract_ffis, flatten? *)
val stub_ffi_types_def = Define `
  stub_ffis_types prog = LIST_FILL (Te_func ffi_type) (FCARD (extract_ffis (flatten prog)))
`

val compile_ffi_type_second = Q.store_thm("compile_ffi_type_second",
  `(m, ffis) = compile_to_module conf asm_conf bitmaps p ==> (EL 1 m.types) = ffi_type`
  fs [stack_to_wasmTheory.compile_to_module_def, stack_to_wasmTheory.wrap_main_def] >>
  simp [] >>
  cheat
)

(* TODO: Do we need correctness theorems for create_memory? *)
val compile_to_module_valid = Q.store_thm("compile_to_module_valid",
`
 (!m ffis conf asm_conf bitmaps prog.
     (m, ffis) = compile_to_module conf asm_conf bitmaps (prog: ((num, ('a stackLang$prog)) alist))
   ==>
     (?mt. typ_module m
       (* Imports should be the correct number of functions with an FFI-like signature. *)
       (stub_ffi_types prog)
       (* Memory should be exported. TODO: Should we also check its type (=size)? *)
       [Te_mem mt; Te_func (main_type W64 (* (wasm_width (:'a)) *))]
     )
 )
`,
rpt strip_tac >>
cheat
)

val stub_ffis_typ = Q.store_thm("stub_ffis_typ"
`(!module ffi store (?ck store'.
    module = compile_to_module conf asm_conf bitmaps (prog: ((num, ('a stackLang$prog)) alist)) /\
    ffi_types = stub_ffi_types prog /\
    ffis = stub_ffis (LENGTH ffi_types) /\
    SOME (moduleinst, store') = instantiate_assuming_validity ffi ck store module ffis
  ) =>
    LIST_REL (\v t. typ_externval store v = SOME t) ffis ffi_types
)`,
cheat
)

val ffi_name_to_import_to_ffi_name = Q.store_thm("ffi_names_to_import_to_ffi_name",
  `EL (w2n ti) m.types = ffi_type ==> import_to_ffi_name m (ffi_name_to_import ti name) = SOME name`,
  rw [wasmSemTheory.import_to_ffi_name_def,stack_to_wasmTheory.ffi_name_to_import_def] >>
  rw [wasmLangTheory.string_to_name_to_string]
)

(* TODO: This is copied from stack_to_lab. Adjust s.t. the following
 * match up:
 *  s.regs                 with some t.store.globals
 *  s.fp_regs              with some t.store.globals
 *  s.memory and s.mdomain with mem0 t
 *  t.clock                with s.clock (maybe not exactly the same, hmm...)
 *
 * We ignore (for now):
 *  install
 *  compile_oracle
 *  code_buffer
 *
 * Additional assumptions made on t:
 * For every foreign function, there is some host function instance
 * that represents it.
 *
 *)
val state_rel_def = Define `
  state_rel (s:('a,'c,'ffi)stackSem$state) (t:('ffi)wasmSem$state) <=>
    (∀n v. FLOOKUP s.regs n = SOME v ⇒ t.regs n = v) ∧
    (∀n v. FLOOKUP s.fp_regs n = SOME v ⇒ t.fp_regs n = v) ∧
    t.mem = s.memory ∧
    t.mem_domain = s.mdomain ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    (∀n prog. lookup n s.code = SOME prog ⇒
      call_args prog t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg ∧
      ∃pc. code_installed pc
             (append (FST (flatten prog n (next_lab prog 1)))) t.code ∧
           loc_to_pc n 0 t.code = SOME pc) ∧
    (* These two conjuncts are needed for Install *)
    domain s.code = set (MAP Section_num t.code) ∧
    EVERY sec_labels_ok t.code ∧
    ¬t.failed ∧
    t.link_reg ≠ t.len_reg ∧ t.link_reg ≠ t.ptr_reg ∧
    t.link_reg ≠ t.len2_reg ∧ t.link_reg ≠ t.ptr2_reg ∧
    ~(t.link_reg ∈ s.ffi_save_regs) /\
    (* TODO: t has no io_regs *)
    (* (!k n. k ∈ s.ffi_save_regs ==> t.io_regs n k = NONE) /\ *)
    (* might need to be cc_save_regs *)
    (* TODO: t has no cc_regs *)
    (* (!k n. k ∈ s.ffi_save_regs ==> t.cc_regs n k = NONE) /\ *)
    (∀x. x ∈ s.mdomain ⇒ w2n x MOD (dimindex (:'a) DIV 8) = 0) ∧
    (* TODO: t has no code_buffer *)
    (* os.code_buffer = t.code_buffer ∧ *)
    (* TODO: t has no compile, compile_oracle *)
    (* s.compile = (λc p. t.compile c (MAP prog_to_section p)) ∧ *)
    (* (t.compile_oracle = λn. let (c,p,_)  = s.compile_oracle n in *)
    (*                        (c,MAP prog_to_section p)) ∧ *)
    (* TODO: t has no len_reg etc. *)
    (* (∀k. let (c,ps,_) = s.compile_oracle k in *)
    (*   EVERY (λ(n,p). *)
    (*     call_args p t.ptr_reg t.len_reg t.ptr2_reg t.len2_reg t.link_reg ∧ *)
    (*     EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0) (extract_labels p) ∧ *)
    (*     ALL_DISTINCT (extract_labels p)) ps ∧ *)
    (*     (* This last conjunct might not be necessary *) *)
    (*     ALL_DISTINCT (MAP FST ps) ) ∧ *)
    ¬s.use_stack ∧
    ¬s.use_store ∧
    ¬s.use_alloc ∧
    ¬s.be (* wasm spec is little endian *)`;

(* val evaluate_nop_rel = Q.store_thm("evaluate_nop_rel", *)
(* ) *)

(* TODO: We should prove that stack_to_wasm produces valid code,
 * and consequently no TypeErrors can occcur. *)

(* TODO: What is the difference between stackSem$Result and stackSem$Halt?
 * It seems that Result is what a function call would return. *)
val sim_r_def = Define `
  sim_r (stackSem$Result   r) (wasmSemanticPrimitives$Result   (SOME (word_loc_to_val r))) /\
  sim_r (stackSem$Halt     r) (wasmSemanticPrimitives$Result   (SOME (word_loc_to_val r))) /\
  sim_r (stackSem$TimeOut   ) (wasmSemanticPrimitives$Timeout   ) /\
  sim_r (stackSem$FinalFFI r) (wasmSemanticPrimitives$FinalFFI r) /\
`

val halt_word_view_def = Define`
  (halt_word_view (Word 0w) = Halt Success) ∧
  (halt_word_view (Word _)  = Halt Resource_limit_hit) ∧
  (halt_word_view _ = Error)`;
val _ = export_rewrites["halt_word_view_def"];

val halt_view_def = Define`
  (halt_view (SOME (Halt w)) = SOME (halt_word_view w)) ∧
  (halt_view (SOME (FinalFFI outcome)) = SOME (Halt(FFI_outcome outcome))) ∧
  (halt_view _ = NONE)`

val _ = export_rewrites["halt_view_def"];

(* Variables "1" are on the stackLang side, and "2" on the WebAssembly side. *)
val compile_correct = Q.store_thm("compile_correct"
  `
    !p1 s1 r1 s1' s2.
    evaluate (p1, s1) = (r1, s1') /\ r1 <> stackSem$Error /\
    sims_s s1 s2 /\
    (?ck_init. s2 = instantiate_with_stubbed_ffi s1.ffi 0n (compile_to_module conf p1))
  ==>
    ?ck r2 s2'.
    invoke_from (s2 with clock := s2.clock + ck) a (* TODO: Obtain a somehow. *) [] = (r2, s2') /\
    sim_s s1' s2' /\ sim_r r1 r2
  `,
  recInduct `stackSemTheory_evaluate_ind` >>
  cheat
)

val _ = export_theory();
