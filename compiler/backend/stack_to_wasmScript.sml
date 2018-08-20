open preamble stackLangTheory labLangTheory (* TODO: Get rid of labLang *) wasmLangTheory;
local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

val _ = new_theory "stack_to_wasm";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = temp_overload_on ("Asm",``λa. Asm (Asmi a)``);

val compile_jump_def = Define `
  (compile_jump (INL n) = LabAsm (Jump (Lab n 0)) 0w [] 0) /\
  (compile_jump (INR r) = Asm (JumpReg r) [] 0)`;

val negate_def = Define `
  (negate Less = NotLess) /\
  (negate Equal = NotEqual) /\
  (negate Lower = NotLower) /\
  (negate Test = NotTest) /\
  (negate NotLess = Less) /\
  (negate NotEqual = Equal) /\
  (negate NotLower = Lower) /\
  (negate NotTest = Test)`

val _ = export_rewrites ["negate_def"];

val _ = temp_overload_on("++",``misc$Append``)

(* Function to map basic instructions. The following does not cover all instrs,
 * but only those for which stackSem$inst actually defines a semantics. *)
val _ = Define `
  flatten_instr (Inst x) =
    dtcase x of
      | Skip => SOME [Noop]
      | Const reg w => NONE
      | Arith (Binop bop r1 r2 ri) => NONE
      | Arith (Shift sh r1 r2 n) => NONE
      | Arith (Div r1 r2 r3) => NONE
      | Arith (AddCarry r1 r2 r3 r4) => NONE
      | Arith (AddOverflow r1 r2 r3 r4) => NONE
      | Arith (SubOverflow r1 r2 r3 r4) => NONE
      | Arith (LongMul r1 r2 r3 r4) => NONE
      | Arith (LongDiv r1 r2 r3 r4 r5) => NONE
      | Mem Load r (Addr a w) => NONE
      | Mem Load8 r (Addr a w) => NONE
      | Mem Store r (Addr a w) => NONE
      | Mem Store8 r (Addr a w) => NONE
      | FP (FPLess r d1 d2) => NONE
      | FP (FPLessEqual r d1 d2) => NONE
      | FP (FPEqual r d1 d2) => NONE
      | FP (FPMov d1 d2) => NONE
      | FP (FPAbs d1 d2) => NONE
      | FP (FPNeg d1 d2) => NONE
      | FP (FPSqrt d1 d2) => NONE
      | FP (FPAdd d1 d2 d3) => NONE
      | FP (FPSub d1 d2 d3) => NONE
      | FP (FPMul d1 d2 d3) => NONE
      | FP (FPDiv d1 d2 d3) => NONE
      | FP (FPMovToReg d r1 r2) => NONE
      | FP (FPMovFromReg d r1 r2) => NONE
      | FP (FPToInt d1 d2) => NONE
      | FP (FPFromInt d1 d2) => NONE
      | _ => NONE`

(*

local val flatten_quotation = `
  flatten p n m =
    dtcase p of
    | Tick => SOME [Noop] (* (List [Asm (Inst (Skip)) [] 0],F,m) *)
    | Inst a => SOME [flatten_instr (Inst a)](* (List [Asm (Inst a) [] 0],F,m) *)
    | Halt _ => NONE (* (List [LabAsm Halt 0w [] 0],T,m) *)
    | Seq p1 p2 => NONE
        (* let (xs,nr1,m) = flatten p1 n m in *)
        (* let (ys,nr2,m) = flatten p2 n m in *)
        (*   (xs ++ ys, nr1 ∨ nr2, m) *)
    | If c r ri p1 p2 => NONE
        (* let (xs,nr1,m) = flatten p1 n m in *)
        (* let (ys,nr2,m) = flatten p2 n m in *)
        (*   if (p1 = Skip) /\ (p2 = Skip) then (List [],F,m) *)
        (*   else if p1 = Skip then *)
        (*     (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++ *)
        (*      List [Label n m 0],F,m+1) *)
        (*   else if p2 = Skip then *)
        (*     (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++ *)
        (*      List [Label n m 0],F,m+1) *)
        (*   else if nr1 then *)
        (*     (List [LabAsm (JumpCmp (negate c) r ri (Lab n m)) 0w [] 0] ++ xs ++ *)
        (*      List [Label n m 0] ++ ys,nr2,m+1) *)
        (*   else if nr2 then *)
        (*     (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++ *)
        (*      List [Label n m 0] ++ xs,nr1,m+1) *)
        (*   else *)
        (*     (List [LabAsm (JumpCmp c r ri (Lab n m)) 0w [] 0] ++ ys ++ *)
        (*      List [LabAsm (Jump (Lab n (m+1))) 0w [] 0; Label n m 0] ++ xs ++ *)
        (*      List [Label n (m+1) 0],nr1 ∧ nr2,m+2) *)
    | While c r ri p1 => NONE (* TODO: Translate to Loop *)
        (* let (xs,_,m) = flatten p1 n m in *)
        (*   (List [Label n m 0; LabAsm (JumpCmp (negate c) r ri (Lab n (m+1))) 0w [] 0] ++ *)
        (*    xs ++ List [LabAsm (Jump (Lab n m)) 0w [] 0; Label n (m+1) 0],F,m+2) *)
    | Raise r => NONE (* (List [Asm (JumpReg r) [] 0],T,m) *) (* TODO: Implement exception handling. *)
    | Return r _ => NONE (* (List [Asm (JumpReg r) [] 0],T,m) *) (* TODO: Translate to Return *)
    | Call NONE dest handler => NONE (* (List [compile_jump dest],T,m) *) (* TODO: Translate to Call *)
    | Call (SOME (p1,lr,l1,l2)) dest handler => NONE
        (* let (xs,nr1,m) = flatten p1 n m in *)
        (* let prefix = List [LabAsm (LocValue lr (Lab l1 l2)) 0w [] 0; *)
        (*          compile_jump dest; Label l1 l2 0] ++ xs in *)
        (* (dtcase handler of *)
        (* | NONE => (prefix, nr1, m) *)
        (* | SOME (p2,k1,k2) => *)
        (*     let (ys,nr2,m) = flatten p2 n m in *)
        (*       (prefix ++ (List [LabAsm (Jump (Lab n m)) 0w [] 0; Label k1 k2 0] ++ *)
        (*       ys ++ List [Label n m 0]), nr1 ∧ nr2, m+1)) *)
    | JumpLower r1 r2 target => NONE (* TODO: Br_if *)
        (* (List [LabAsm (JumpCmp Lower r1 (Reg r2) (Lab target 0)) 0w [] 0],F,m) *)
    | FFI ffi_index _ _ _ _ lr => NONE (* (List [LabAsm (LocValue lr (Lab n m)) 0w [] 0; *)
                                       (*   LabAsm (CallFFI ffi_index) 0w [] 0; *)
                                       (*   Label n m 0],F,m+1) *)
    | LocValue i l1 l2 => NONE (* (List [LabAsm (LocValue i (Lab l1 l2)) 0w [] 0],F,m) *) (* TODO: What is this? *)
    | Install _ _ _ _ ret => NONE (* TODO: Left out in first implementation. *)
    | CodeBufferWrite r1 r2 => NONE (* TODO: Left out in first implementation. *)
    | _  => NONE`
in
val flatten_def = Define flatten_quotation

val flatten_pmatch = Q.store_thm("flatten_pmatch",`∀p n m.` @
  (flatten_quotation |>
   map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE
       | aq => aq)),
  rpt strip_tac
  >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true)
  >> rpt strip_tac
  >> rw[Once flatten_def,pairTheory.ELIM_UNCURRY] >> every_case_tac >> fs[]);
end

val prog_to_section_def = Define `
  prog_to_section (n,p) =
    let (lines,_,m) = (flatten p n (next_lab p 1)) in
      Section n (append (Append lines (List [Label n m 0])))`

val is_gen_gc_def = Define `
  (is_gen_gc (Generational l) = T) /\
  (is_gen_gc _ = F)`

val _ = Datatype`config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>`;

val compile_def = Define `
 compile stack_conf data_conf max_heap sp offset prog =
   let prog = stack_alloc$compile data_conf prog in
   let prog = stack_remove$compile stack_conf.jump offset (is_gen_gc data_conf.gc_kind)
                max_heap sp InitGlobals_location prog in
   let prog = stack_names$compile stack_conf.reg_names prog in
     MAP prog_to_section prog`;
*)
val _ = export_theory();
