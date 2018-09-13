open preamble
     stackSemTheory stackPropsTheory
     wasmSemTheory

val _ = new_theory "stack_to_wasmProof"

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

val _ = export_theory();
