open preamble stackLangTheory wasmLangTheory;
local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

val _ = new_theory "stack_to_wasm";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val flip_def = Define `
  (flip Less = NotLess) /\
  (flip Equal = NotEqual) /\
  (flip Lower = NotLower) /\
  (flip Test = NotTest) /\
  (flip NotLess = Less) /\
  (flip NotEqual = Equal) /\
  (flip NotLower = Lower) /\
  (flip NotTest = Test)`

val _ = export_rewrites ["flip_def"];

val _ = temp_overload_on("++",``misc$Append``)

(* See stackSem$evaluate If ..., and labSem$word_cmp *)
(* TODO: This function should push the values that are to be compared on
 * the stack and jmp the appropriate relop/testop, such that a boolean
 * is left on the stack. *)
val compile_cmp_def = Define `
  compile_cmp c r ri = []`

(* Function to map basic instructions. The following does not cover all instrs,
 * but only those for which stackSem$inst actually defines a semantics. *)
val _ = Define `
  flatten_instr (Inst x) =
    dtcase x of
      | Skip => [Nop]
      | Const reg w => [] (* TODO *)
      | Arith (Binop bop r1 r2 ri) => [] (* TODO *)
      | Arith (Shift sh r1 r2 n) => [] (* TODO *)
      | Arith (Div r1 r2 r3) => [] (* TODO *)
      | Arith (AddCarry r1 r2 r3 r4) => [] (* TODO *)
      | Arith (AddOverflow r1 r2 r3 r4) => [] (* TODO *)
      | Arith (SubOverflow r1 r2 r3 r4) => [] (* TODO *)
      | Arith (LongMul r1 r2 r3 r4) => [] (* TODO *)
      | Arith (LongDiv r1 r2 r3 r4 r5) => [] (* TODO *)
      | Mem Load r (Addr a w) => [] (* TODO *)
      | Mem Load8 r (Addr a w) => [] (* TODO *)
      | Mem Store r (Addr a w) => [] (* TODO *)
      | Mem Store8 r (Addr a w) => [] (* TODO *)
      | FP (FPLess r d1 d2) => [] (* TODO *)
      | FP (FPLessEqual r d1 d2) => [] (* TODO *)
      | FP (FPEqual r d1 d2) => [] (* TODO *)
      | FP (FPMov d1 d2) => [] (* TODO *)
      | FP (FPAbs d1 d2) => [] (* TODO *)
      | FP (FPNeg d1 d2) => [] (* TODO *)
      | FP (FPSqrt d1 d2) => [] (* TODO *)
      | FP (FPAdd d1 d2 d3) => [] (* TODO *)
      | FP (FPSub d1 d2 d3) => [] (* TODO *)
      | FP (FPMul d1 d2 d3) => [] (* TODO *)
      | FP (FPDiv d1 d2 d3) => [] (* TODO *)
      | FP (FPMovToReg d r1 r2) => [] (* TODO *)
      | FP (FPMovFromReg d r1 r2) => [] (* TODO *)
      | FP (FPToInt d1 d2) => [] (* TODO *)
      | FP (FPFromInt d1 d2) => [] (* TODO *)
      | _ => [] (* TODO *)`

(* TODO: Implement this ... *)
val reg_to_global = Define `reg_to_global n = n2w n`
val set_lab_def = Define `set_lab = Set_global (n2w 42n)`
val set_seg_def = Define `set_seg = Set_global (n2w 43n)`
val continue_def = Define `continue n m = Br (n2w (n + m))`

val get_reg = Define `get_reg r = Get_global (reg_to_global r)`

val jmp_indirect_def = Define `jmp_indirect n m r = [
            get_reg r; Wrap; set_lab;
            get_reg r; (Const (V_i32 32w)) Shr U; Wrap; set_seg;
            continue n m
        ]`

val jmp_def = Define `jmp n m n' m' = [Const (V_i32 (n2w n')); set_seg; (Const V_i32 (n2w m')); set_lab; continue n m]`
val jmp_if_def = Define `jmp_if n m c r ri n' m' = (compile_cmp c r ri) ++ [If (jmp n m n' m') []]`

val compile_jump_def = Define `
(compile_jump n' m' (INL n) = jmp          n' m' n 0) /\
(compile_jump n' m' (INR r) = jmp_indirect n' m' r)`;

val switch_def = Define `switch r bs = FOLDR (\x acc. Block [] acc::x) [Block [] [get_reg r; Br_table (GENLIST (\i. n2w (i + 1)) (LENGTH bs)) 0w]] bs`

val lab_def = Define `lab = List [Block [] []]`

val simple_if_def = Define `simple_if n m c r ri l1 l2 other =
  (List (jmp_if n m c r ri n m) ++ l1 ++ lab ++ l2, other, m + 1)`

val splitall_def = Define `splitall p xs = FOLDR (\x acc. if p x then CONS [] acc else (CONS (CONS x (HD acc)) (TL acc))) [] xs`
val lab2reg_def = Define `lab2reg i l1 l2 = [(Const (V_i64 (word_or (word_lsl (n2w l1) 32) (n2w l2)))); set_reg i]`

(* Go from top to bottom, and when a new lab is requested: Generate a new Block, put the *)
(* own code afterwards and recurse into the block. *)
local val flatten_quotation = `
  flatten p n m =
    dtcase p of
    | Tick => (List [Noop], F, m)
    | Inst a => (List (compile_inst a), F, m)
    | Halt _ => (List [], T, m) (* TODO: Set some flag that will stop execution. *)

    | Seq p1 p2 =>
        let (l1, nr1, m) = flatten p1 n ;
            (l2, nr2, m) = flatten p2 n in
            (l1 ++ l2, nr1 \/ nr2, m)

    | If c r ri Skip Skip => (List [], F, m)
    | If c r ri Skip p2   => simple_if n m       c  r ri p2 [] F
    | If c r ri p1   Skip => simple_if n m (flip c) r ri p1 [] F
    | If c r ri p1   p2   =>
          let (l1, nr1, m) = flatten p1 n m ;
              (l2, nr2, m) = flatten p2 n m in
                   if nr1 then simple_if n m (flip c) r ri l1 l2 nr2
              else if nr2 then simple_if n m       c  r ri l2 l1 nr1
              else
                  (List (jmp_if n m c r ri n  m     )        ++ l2 ++
                   List (jmp    n m        n (m + 1)) ++ lab ++ l1 ++ lab, F, m + 2)

    | While c r ri p =>
        let (l, _, m) = flatten p n m in
            (lab ++ (jmp_if n (flip c) r ri n (m + 1)) ++ l
                 ++ (jmp    n m             n  m     ) ++ lab, F, m + 2)

    | Raise  r   => (jmp_indirect n m r, T, m)
    | Return r _ => (jmp_indirect n m r, T, m)
    | JumpLower r1 r2 target => (List (jmp_if n Lower r1 (Reg r2) target 0), F, m)

    | Call  NONE                          dest _  => (List (compile_jump n m dest), T, m)
    | Call (SOME (rhp, rhlr, rhl1, rhl2)) dest eh =>
        let (rhi, nr1, m) = flatten rhp n m ;
            prefix = List [lab2reg rhlr rhl1 rhl2] ++ (compile_jump n dest) ++ lab ++ rhi in
        (dtcase eh of
        | NONE => (prefix, nr1, m)
        | SOME (ehp, ehl1, ehl2) =>
          let (ehi, nr2, m) = flatten ehp n m in
              (prefix ++ (List (jmp n m n m) ++ lab ++ ys ++ lab), nr1 /\ nr2, m + 1))

    | FFI ffi_index ptr1 len1 ptr2 len2 _ =>
          (List [
                (Const (V_i32 (n2w ptr1)));
                (Const (V_i32 (n2w len1)));
                (Const (V_i32 (n2w ptr2)));
                (Const (V_i32 (n2w len2)));
                (Call (n2i 0 (* TODO: Find out how to get the correct funcidx! *)))
            ], n)
        (* Since we must use wasm's Call instruction here, we do not emit a new lab,
         * do not deal with the link register, etc.
         * NOTE: We actually do not use the link register even though it was allocated... *)

    | LocValue i l1 l2 => (List (lab2reg i l1 l2), F, m)
    | _  => (List [], F, m)` (* NOTE: Install and CodeBufferWrite are left out in the initial implementation. *)
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

val prog_to_block_def = Define `
  prog_to_block (n,p) =
    let (lines,_,m) = (flatten p n (next_lab p 1)) in
      Block NONE (append (Append lines (List [Lab n m 0])))`
      (* Section n (append (Append lines (List [Lab n m 0])))` *)

val _ = Datatype`config =
  <| reg_names : num num_map
   ; jump : bool (* whether to compile to JumpLower or If Lower ... in stack_remove*)
   |>`;

val compile_def = Define `
 compile stack_conf data_conf max_heap sp offset prog =
   let prog = stack_alloc$compile data_conf prog in
   let prog = stack_remove$compile stack_conf.jump offset T
                max_heap sp InitGlobals_location prog in
   let prog = stack_names$compile stack_conf.reg_names prog in
     MAP prog_to_block prog`;

val _ = export_theory();
