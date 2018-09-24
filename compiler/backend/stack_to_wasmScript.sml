open preamble stackLangTheory wasmLangTheory

(* NOTE: wasm behaves differently compared to the alternative
 *       branch (stack->lab->target) in that it will encode
 *       to bytes directly. The exporter then does "nothing".
 *       This is to keep compatiblity. *)
open wasm_binaryTheory

local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

(* Parts of this translation currently assume a 64bit architecture, i.e. all stackLang
 * registers are modeled as i64 globals. It would be possible to implement this
 * dependent on the stackLang word with and switch to i32 in case the stackLang
 * word with is smaller than or equal to 32bits, but that would introduce some
 * complications into the compiler that are desirable and reasonable to avoid
 * in a first implementation. *)

val _ = new_theory "stack_to_wasm";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES ()

val _ = Datatype `config = <| heap_sz: num; stack_sz: num |>`

val flip_def = Define `
  (flip Equal    = NotEqual) /\
  (flip Lower    = NotLower) /\
  (flip Less     = NotLess ) /\
  (flip Test     = NotTest ) /\
  (flip NotEqual = Equal   ) /\
  (flip NotLower = Lower   ) /\
  (flip NotLess  = Less    ) /\
  (flip NotTest  = Test    )`

val _ = export_rewrites ["flip_def"];

val _ = temp_overload_on("++",``misc$Append``)

val compile_binop_def = Define `
  compile_binop x= case x of
    | asm$Add => wasmLang$Add
    | asm$Sub => wasmLang$Sub
    | asm$And => wasmLang$And
    | asm$Or  => wasmLang$Or
    | asm$Xor => wasmLang$Xor
`

val compile_shift_def = Define `
  compile_shift x = case x of
    | Lsl => Shl
    | Lsr => Shr U
    | Asr => Shr S
    | Ror => Rotr
`

(* val flatten_def = Define `flatten = FLAT o (MAP SND)` *)
val flatten_def = Define `flatten (sections:((num, ('a stackLang$prog)) alist)) = FOLDR (\x acc. stackLang$Seq x acc) Tick ((MAP SND) sections)`
val uniq_def = Define `uniq = SET_TO_LIST o LIST_TO_SET`

(* Applies f to all "terminals" in p, i.e. all excluding
 * Seq, Call, If, While. *)
val foldl_prog_def = Define `
  foldl_prog f e p =
    dtcase p of
      | Seq p1 p2 => foldl_prog f (foldl_prog f e p1) p2

      | Call rh _ eh =>
        let e = (case rh of SOME (p1, _) => foldl_prog f e p1 | NONE => e) in
                (case eh of SOME (p2, _) => foldl_prog f e p2 | NONE => e)

      | If    _ _ _ p1 p2 => foldl_prog f (foldl_prog f e p1) p2
      | While _ _ _ p1    =>               foldl_prog f e p1

      | p => f p e`

val extract_ffi_names_def = Define `
  extract_ffi_names prog = alist_to_fmap (MAPi
  (\i name. (name, n2w_itself (i, (:32))))
  (uniq (foldl_prog (\p acc.
    case p of
      | FFI name _ _ _ _ _ => name :: acc
      | _                  =>         acc
  ) [] prog)))`


val global_for_reg_count_def = Define `global_for_reg_count asm_conf = asm_conf.reg_count - (LENGTH asm_conf.avoid_regs)`
val global_for_fp_reg_count_def = Define `global_for_fp_reg_count asm_conf = asm_conf.fp_reg_count`
val global_for_program_count_def = Define `global_for_program_count asm_conf = (global_for_reg_count asm_conf) + (global_for_fp_reg_count asm_conf)`

val reg_to_global_def = Define `reg_to_global n = n2w n`
val fp_reg_to_global_def = Define `fp_reg_to_global asm_conf n = n2w (n + global_for_reg_count asm_conf)`

val seg_global_def = Define `seg_global asm_conf = global_for_program_count asm_conf`
val lab_global_def = Define `lab_global asm_conf = 1 + seg_global asm_conf`

val set_lab_def = Define `set_lab asm_conf = [Set_global (n2w (lab_global asm_conf))]`
val get_lab_def = Define `get_lab asm_conf = [Get_global (n2w (lab_global asm_conf))]`
val set_seg_def = Define `set_seg asm_conf = [Set_global (n2w (seg_global asm_conf))]`
val get_seg_def = Define `get_seg asm_conf = [Get_global (n2w (seg_global asm_conf))]`

val get_reg_def = Define `get_reg r = [Get_global (reg_to_global r)]`
val set_reg_def = Define `set_reg r = [Set_global (reg_to_global r)]`

val get_reg_imm_def = Define `
  get_reg_imm ri width = if width <> W64 then [] else case ri of
    | Reg r => get_reg r
    | Imm i => [wasmLang$Const (V_i64 (w2w i))]
`

val get_fp_reg_def = Define `get_fp_reg asm_conf r = [Get_global (fp_reg_to_global asm_conf r)]`
val set_fp_reg_def = Define `set_fp_reg asm_conf r = [Set_global (fp_reg_to_global asm_conf r)]`

val continue_def = Define `continue n m = [Br (n2w (n + m))]`
val fpop_def = Define `fpop asm_conf result args op = (FLAT (MAP (get_fp_reg asm_conf) args)) ++ op ++ (set_fp_reg asm_conf result)`
val autowrap_def = Define `autowrap W32 = [] /\ autowrap W64 = [Conversion Wrap]`

(* compile_cmp assumes 64bit words! *)
val compile_cmp_def = Define `
  compile_cmp c r ri =
    let (v, vi) = (get_reg r, get_reg_imm ri W64) in
    case c of
    | Equal    => v ++ vi ++ [Relop_i W64 Eq]
    | Lower    => v ++ vi ++ [Relop_i W64 (Lt U)]
    | Less     => v ++ vi ++ [Relop_i W64 (Lt S)]
    | Test     => v ++ [Testop_i W64 Eqz] ++ vi ++ [Testop_i W64 Eqz; Binop_i W64 wasmLang$And]
    | NotEqual => v ++ vi ++ [Relop_i W64 Ne]
    | NotLower => v ++ vi ++ [Relop_i W64 (Ge U)]
    | NotLess  => v ++ vi ++ [Relop_i W64 (Ge S)]
    | NotEqual => v ++ [Testop_i W64 Eqz] ++ vi ++ [Testop_i W64 Eqz; Binop_i W64 wasmLang$And;
                        Const (V_i64 1w); Binop_i W64 wasmLang$Xor]
`

(* Function to map basic instructions. The following does not cover all instrs,
 * but only those for which stackSem$inst actually defines a semantics.
 * Also, width is currently hardcoded for 64bits, but it should be quite easy
 * to refactor it to cover the more general case.
 *)
val compile_inst_def = Define `
  compile_inst (asm_conf: 'a asm$asm_config) (x: 'a inst) =
    let
      width = wasm_width (:'a);
      rt = Tv Ki width;
      vzro = V_i64 0w (* (w2val rt (0w:'a word)) *);
      vone = V_i64 1w (* (w2val rt (1w:'a word)) *);
      get_fp_reg = get_fp_reg asm_conf;
      set_fp_reg = set_fp_reg asm_conf;
      fpop = fpop asm_conf;
    in if width <> W64 then [] else case x of
      | Skip =>
        [Nop]
      | asm$Const reg w =>
        [wasmLang$Const (w2val (Tv Ki width) w)] ++ (set_reg reg)
      | Arith (Binop bop r1 r2 ri) =>
        (get_reg r2) ++ (get_reg_imm ri width) ++ [Binop_i width (compile_binop bop)] ++ (set_reg r1)
      | Arith (Shift sh r1 r2 n) =>
        (get_reg r2) ++ [wasmLang$Const (w2val rt (n2w n:word32))] ++ [Binop_i width (compile_shift sh)] ++ (set_reg r1)
      | Arith (Div r1 r2 r3) =>
        (get_reg r3) ++ (get_reg r2) ++ [Binop_i width (wasmLang$Div U)] ++ (set_reg r1)
      | Arith (AddCarry r1 r2 r3 r4) =>
        (* First, make sure carry is either one or zero, to avoid surprises. *)
        (* stackSem: if c = 0w then 0 else 1 *)
        (get_reg r4) ++ [Testop_i width Eqz; wasmLang$If [rt] [Const vzro] [Const vone]] ++ (set_reg r4) ++
        (* Add the two arguments. *)
        (get_reg r2) ++ (get_reg r3) ++ [Binop_i width wasmLang$Add] ++
        (* Save the (maybe overflown) result, and push it again (no instruction to duplicate TOS). *)
        (set_reg r1) ++ (get_reg r1) ++
        (* Check for overflow by comparing against one operand. *)
        (get_reg r2) ++ [Relop_i width (Lt U)] ++
        [wasmLang$If [rt]
          (
            (* 1: Addition overflowed, it is now safe to add the carry. *)
            (get_reg r1) ++ (get_reg r4) ++ [Binop_i width wasmLang$Add] ++
            (* The new carry is one. *)
            [Const vone]
          )
          (
            (* 2: Addition did not overflow, so adding the carry might still overflow (to zero). *)
            (* Instead of just adding carry, we check whether it is zero. *)
            (get_reg r4) ++ [Testop_i width Eqz] ++
            [wasmLang$If [Tv Ki width] [] (
              (get_reg r1) ++ [Const vone] ++ (set_reg r1) ++
              (get_reg r1) ++ [Testop_i width Eqz] ++ (autowrap width)
            )]
          )
        ]
        ++ (set_reg r4)
      | Arith (AddOverflow r1 r2 r3 r4) =>
        (* Add the two arguments. *)
        (get_reg r2) ++ (get_reg r3) ++ [Binop_i width Add] ++
        (* Save the (maybe overflown) result, and push it again (no instruction to duplicate TOS). *)
        (set_reg r1) ++ (get_reg r1) ++
        (* Check for overflow by comparing against one operand. This gives us the carry bit. *)
        (get_reg r2) ++ [Relop_i width (Lt U)] ++ (autowrap width) ++ (set_reg r4)
      | Arith (SubOverflow r1 r2 r3 r4) => [] (* TODO *)
      | Arith (LongMul r1 r2 r3 r4) => [] (* TODO *)
      | Arith (LongDiv r1 r2 r3 r4 r5) => [] (* TODO *)
      | Mem Load   r (Addr a w) =>
        (get_reg a) ++ (autowrap width) ++ [Load (Tv Ki width) <| offset := (w2w w); align := 0w |>] ++ (set_reg r)
      | Mem Load8  r (Addr a w) =>
        (get_reg a) ++ (autowrap width) ++ [Loadi width S8 U <| offset := (w2w w); align := 0w |>] ++ (set_reg r)
      | Mem Store  r (Addr a w) =>
        (get_reg r) ++ (get_reg a) ++ (autowrap width) ++ [Store (Tv Ki width) <| offset := (w2w w); align := 0w |>]
      | Mem Store8 r (Addr a w) =>
        (get_reg r) ++ (get_reg a) ++ (autowrap width) ++ [Storei width S8 <| offset := (w2w w); align := 0w |>] ++ (set_reg r)
      | FP (FPLess r d1 d2) =>
        (get_fp_reg d1) ++ (get_fp_reg d2) ++ [Relop_f W64 Ltf] ++ (set_reg r)
      | FP (FPLessEqual r d1 d2) =>
        (get_fp_reg d1) ++ (get_fp_reg d2) ++ [Relop_f W64 Lef] ++ (set_reg r)
      | FP (FPEqual r d1 d2) =>
        (get_fp_reg d1) ++ (get_fp_reg d2) ++ [Relop_f W64 Eqf] ++ (set_reg r)
      | FP (FPMov d1 d2) =>
        fpop d1 [d2    ] [Nop]
      | FP (FPAbs d1 d2) =>
        fpop d1 [d2    ] [Unop_f W64 Absf]
      | FP (FPNeg d1 d2) =>
        fpop d1 [d2    ] [Unop_f W64 Negf]
      | FP (FPSqrt d1 d2) =>
        fpop d1 [d2    ] [Unop_f W64 Sqrtf]
      | FP (FPAdd d1 d2 d3) =>
        fpop d1 [d2; d3] [Binop_f W64 Addf]
      | FP (FPSub d1 d2 d3) =>
        fpop d1 [d2; d3] [Binop_f W64 Subf]
      | FP (FPMul d1 d2 d3) =>
        fpop d1 [d2; d3] [Binop_f W64 Mulf]
      | FP (FPDiv d1 d2 d3) =>
        fpop d1 [d2; d3] [Binop_f W64 Divf]
      | FP (FPMovToReg r1 r2 d) =>
        (* Sadly, there is no instruction to duplicate a value... *)
        let conversion = (get_fp_reg d) ++ [Conversion (Reinterpret T_f64)] in
          conversion ++ (
            if width = W64
            then set_reg r1
            else conversion                                                                ++
                 [Conversion Wrap                                        ] ++ (set_reg r1) ++
                 [Const (V_i64 32w); Binop_i W64 (Shr U); Conversion Wrap] ++ (set_reg r2)
          )
      | FP (FPMovFromReg d r1 r2) =>
        (get_reg r1) ++
        (
          if width = W64
          then []
          else [Conversion (Extend U)] ++
               (get_reg r2) ++
               [Conversion (Extend U); Const (V_i64 32w); Binop_i W64 Shl] ++
               [Binop_i W64 Or]
        ) ++ [Conversion (Reinterpret T_i64)] ++ (set_fp_reg d)
      | FP (FPToInt d1 d2) => []
      | FP (FPFromInt d1 d2) =>
        (get_fp_reg d2) ++ [
          (* Convert to i64 so we can do bitwise operations. *)
          Conversion (Reinterpret T_f64)
        ] ++ (if width = W64 \/ EVEN d2 then [
          (* Mask to get 32 LSBs, but keep sign for conversion. *)
          Const (V_i64 0x80000000FFFFFFFFw); Binop_i W64 And
        ] else if ODD d2 then [
          (* Shift to get 32 MSBs, but keep sign for conversion. *)
          Const (V_i64 32w); Binop_i W64 (Shr S)
        ] else []) ++ [
          Conversion (Convert W64 S W64)
        ] ++ (set_fp_reg d1)
     | _ => []
`

val jmp_indirect_def = Define `
  jmp_indirect asm_conf n m r w =
    (get_reg r) ++ (
      if w = W32
      then [Conversion Wrap]
      else [Const (V_i32 0xFFFFw); Binop_i W32 And]
    ) ++ (set_lab asm_conf) ++
    (get_reg r) ++ (
        if w = W32
        then [Const (V_i32 16w); Binop_i W32 (Shr U)]
        else [wasmLang$Const (V_i64 32w); Binop_i W64 (Shr U); Conversion Wrap]
    ) ++ (set_seg asm_conf) ++
    continue n m
`

val jmp_def = Define `
  jmp asm_conf n m n' m' =
    [wasmLang$Const (V_i32 (n2w n'))] ++ (set_seg asm_conf) ++
    [wasmLang$Const (V_i32 (n2w m'))] ++ (set_lab asm_conf) ++
    (continue n m)
`

val jmp_if_def = Define `jmp_if asm_conf n m c r ri n' m' = ((compile_cmp c r ri) ++ [wasmLang$If [] (jmp asm_conf n m n' m') []])`

val compile_jump_def = Define `
(compile_jump asm_conf n' m' (INL n) w = jmp          asm_conf n' m' n 0) /\
(compile_jump asm_conf n' m' (INR r) w = jmp_indirect asm_conf n' m' r w)`;

val switch_def = Define `
  switch v bs = FOLDR
    (\x acc. Block [] acc::x)
    [Block [] (v ++ [Br_table (to_nlist (GENLIST (\i. n2w (i + 1)) (LENGTH bs))) 0w])]
    bs
`

val lab_def = Define `lab = [Block [] []]`

val simple_if_def = Define `simple_if asm_conf n m c r ri l1 l2 other =
  ((jmp_if asm_conf n m c r ri n m) ++ l1 ++ lab ++ l2, other, m + 1)`

val splitall_def = Define `splitall p xs = FOLDR (\x acc. if p x then CONS [] acc else (CONS (CONS x (HD acc)) (TL acc))) [] xs`
val lab2reg_def = Define `lab2reg i l1 l2 = [(wasmLang$Const (V_i64 (word_or (word_lsl (n2w l1) 32) (n2w l2))))] ++ (set_reg i)`

(* Go from top to bottom, and when a new lab is requested: Generate a new Block, put the *)
(* own code afterwards and recurse into the block. *)
(* At the moment, we require the list of ffis so we can index into the wasm funcs. That's
 * slightly, annoying. Maybe there's a nicer way. *)
local val compile_section_quotation = `
  compile_section (asm_conf: 'a asm$asm_config) (ffis: string |-> funcidx) (p:'a stackLang$prog) n m =
    let width = wasm_width (:'a) in
    if width <> W64 then ([Unreachable], T, 0) else
    dtcase p of
    | Tick => ([Nop], F, m)
    | Inst a => (compile_inst asm_conf a, F, m)
    | Halt r1 => ((get_reg r1) ++ [Return], T, m)

    | Seq p1 p2 =>
      let (l1, nr1, m) = compile_section asm_conf ffis p1 n m ;
          (l2, nr2, m) = compile_section asm_conf ffis p2 n m in
        (l1 ++ l2, nr1 \/ nr2, m)

    | stackLang$If c r ri p1   p2   =>
      if p1 = Skip /\ p2 = Skip then ([], F, m) else
      if p1 = Skip then let (l2, nr2, m) = compile_section asm_conf ffis p2 n m in simple_if asm_conf n m       c  r ri l2 [] F else
      if p2 = Skip then let (l1, nr1, m) = compile_section asm_conf ffis p1 n m in simple_if asm_conf n m (flip c) r ri l1 [] F else
      let (l1, nr1, m) = compile_section asm_conf ffis p1 n m ;
          (l2, nr2, m) = compile_section asm_conf ffis p2 n m in
             if nr1 then simple_if asm_conf n m (flip c) r ri l1 l2 nr2
        else if nr2 then simple_if asm_conf n m       c  r ri l2 l1 nr1
        else
          ((jmp_if asm_conf n m c r ri n  m     )        ++ l2 ++
           (jmp    asm_conf n m        n (m + 1)) ++ lab ++ l1 ++ lab, F, m + 2)

    | While c r ri p =>
      let (l, _, m) = compile_section asm_conf ffis p n m in
          (lab ++ (jmp_if asm_conf n m (flip c) r ri n (m + 1)) ++ l
               ++ (jmp    asm_conf n m               n  m     ) ++ lab, F, m + 2)

    | Raise  r   => (jmp_indirect asm_conf n m r width, T, m)
    | Return r _ => (jmp_indirect asm_conf n m r width, T, m)
    | JumpLower r1 r2 target => (jmp_if asm_conf n m Lower r1 ((Reg r2):'a reg_imm) target 0, F, m)

    | stackLang$Call  NONE                          dest _  => (compile_jump asm_conf n m dest width, T, m)
    | stackLang$Call (SOME (rhp, rhlr, rhl1, rhl2)) dest eh =>
      let (rhi, nr1, m) = compile_section asm_conf ffis rhp n m ;
          prefix = (lab2reg rhlr rhl1 rhl2) ++ (compile_jump asm_conf n m dest width) ++ lab ++ rhi in
        (dtcase eh of
        | NONE => (prefix, nr1, m)
        | SOME (ehp, ehl1, ehl2) =>
          let (ehi, nr2, m) = compile_section asm_conf ffis ehp n m in
              (prefix ++ (jmp asm_conf n m n m) ++ lab ++ ehi ++ lab, nr1 /\ nr2, m + 1))

    | FFI ffi_name ptr1 len1 ptr2 len2 _ =>
      (case FLOOKUP ffis ffi_name of
        | SOME idx =>
          (* Since we must use wasm's Call instruction here, we do not emit a new lab, *)
          (* do not deal with the link register, etc. *)
          (* NOTE: We actually do not use the link register even though it was allocated... *)
          (* if EXISTS (\n. n > UINT_MAX (:32)) [ptr1;len1;ptr2;len2]then ([Unreachable], F, m) else *)
          ((FLAT (MAP get_reg [ptr1;len1;ptr2;len2])) ++ [Call idx], F, m)
        | _ => ([Unreachable (* to trap execution at runtime. *)], F, m)
      )

    | stackLang$LocValue i l1 l2 => ((lab2reg i l1 l2), F, m)

    (* NOTE: Install and CodeBufferWrite are left out in the initial implementation. *)
    | _  => ([Unreachable (* to trap execution at runtime. *)], F, m)
`
in
val compile_section_def = Define compile_section_quotation

(* val compile_pmatch = Q.store_thm("compile_pmatch",`∀p n m.` @ *)
(*   (compile_quotation |> *)
(*    map (fn QUOTE s => Portable.replace_string {from="dtcase",to="case"} s |> QUOTE *)
(*        | aq => aq)), *)
(*   rpt strip_tac *)
(*   >> CONV_TAC(patternMatchesLib.PMATCH_LIFT_BOOL_CONV true) *)
(*   >> rpt strip_tac *)
(*   >> rw[Once compile_def,pairTheory.ELIM_UNCURRY] >> every_case_tac >> fs[]); *)
end

val section_to_block_def = Define `
  section_to_block asm_conf ffis (n, p) =
    let (lines, _, m) = (compile_section asm_conf ffis p n (next_lab p 1)) in
      switch (get_lab asm_conf) (splitall (\x. [x] = lab) (lab ++ lines))
`

val w2bs_def = Define `w2bs w = (MAP n2w (word_to_oct_list w)):(byte list)`
val ws2bs_def = Define `ws2bs = FLAT o MAP w2bs`

(* CakeML measures in mebibytes (=1MiB), WebAssembly measures in pages (=64KiB) *)
val mebibytes_to_pages_def = Define `mebibytes_to_pages n = (n * 1024n * 1024n) DIV page_size`

(* Calculates how many pages we need to fit a given number of bytes. *)
val fit_pages_def = Define `
fit_pages 0 = 0n /\
fit_pages n = if n < page_size then 1n else 1n + fit_pages (n - page_size)`

val create_memory_def = Define `
  create_memory conf (bitmaps: ('a word) list) =
    let heapnstack = mebibytes_to_pages (conf.heap_sz + conf.stack_sz) in
    let pages = fit_pages ((LENGTH bitmaps) * dimword (:'a)) in
    let size = n2w_itself (pages, (:32)) in
    let mem = <| type := limits_exact size |> in
    let offset = n2w_itself (heapnstack * page_size, (:32)) in
    let bitmap_mark = <| data := 0w ; offset := Expr [Const (V_i32     0w)]; init := ws2bs [0w:word32; offset] |> in
    let bitmap_data = <| data := 0w ; offset := Expr [Const (V_i32 offset)]; init := ws2bs bitmaps |> in
    (mem, [bitmap_mark; bitmap_data])`

(* TODO: Use asm_conf.link_reg for br_table madness instead of two separate globals? *)
(* TODO: This assumes that we have at least four registers. Sounds reasonable, but is not checked. *)
(* See also https://wiki.cakeml.org/startup-halting#startup-code and
 * the startup code of export implementations for other target architectures. *)
val asm_to_globals_def = Define `
  asm_to_globals conf (asm_conf: 'a asm$asm_config) =
    let width = wasm_width (:'a) in
    if width <> W64 then [] else
    let reg_t = Tv Ki width in
    let heap_sz = conf.heap_sz * 1024n * 1024n in
    let stack_sz = conf.stack_sz * 1024n * 1024n in
    let cake_heap = 0n in
    let cake_stack = heap_sz in
    let cake_end = cake_stack + stack_sz in
    [
      (* The first four are special, since they must be initialized. *)
      (* The address of main. *)
      global_zero T_var reg_t;
      (* First heap address. *)
      global_zero T_var reg_t;
      (* First stack address. *)
      <| type := T_global T_var reg_t; init := Expr [wasmLang$Const (V_i64 (n2w_itself (cake_stack, (:64))))] |>;
      (* First address after the stack. *)
      <| type := T_global T_var reg_t; init := Expr [wasmLang$Const (V_i64 (n2w_itself (cake_end, (:64))))] |>;
    ] ++
    (* All other ordinary registers. *)
    (GENLIST (\x. global_zero T_var reg_t) (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs) - 4n)) ++
    (* Floating-Point registers. *)
    (GENLIST (\x. global_zero T_var T_f64) asm_conf.fp_reg_count) ++
    (* Two more globals to store next section and label to execute/jump to.
     * Always i32 to match argument type of br_table instruction. *)
    (GENLIST (\x. global_zero T_var T_i32) 2)
`

val ffi_name_to_import_def = Define `
  ffi_name_to_import ffi_type_index ffi_name =
    <| module := ffi_module_name
     ; name := string_to_name ffi_name
     ; desc := Import_func ffi_type_index
     |>`

val main_type_def = Define `main_type width = Tf [] [Tv Ki width]`

val wrap_main_def = Define `
  wrap_main b conf (asm_conf:'a asm$asm_config) (ffis: string |-> word32) (bitmaps:(('a word) list)) =
    let (mem, data) = create_memory conf bitmaps in
    let ffi_names = (MAP FST (fmap_to_alist ffis)) in (
    <| types  := [main_type (wasm_width (:'a)); ffi_type]
     ; funcs  := [<| type := 0w; locals := []; body := Expr b |>]
     ; tables := []
     ; mems   := [mem]
     ; globals:= (asm_to_globals conf asm_conf)
     ; elem   := []
     ; data   := data
     ; start  := NONE (* We cannot use this since our function must return a value. *)
     ; imports:= (MAP (ffi_name_to_import 1w) ffi_names)
     ; exports:= [<| name := string_to_name "memory"; desc := Export_mem  0w|>;
                  <| name := string_to_name "main"  ; desc := Export_func (n2w (LENGTH ffi_names))|>]
     |>, ffi_names)`

val compile_to_module_def = Define `
  compile_to_module conf asm_conf (bitmaps:(('a word) list)) (prog:((num, ('a stackLang$prog)) alist)) =
    (* Extract FFI names. We need a global view on them to
     * generate wasmLang$Call referring by index. *)
    let ffis = extract_ffi_names (flatten prog) in
      wrap_main (switch (get_seg asm_conf) (MAP (section_to_block asm_conf ffis) prog)) conf asm_conf ffis bitmaps
`

val compile_without_encoding_def = Define `
 compile_without_encoding conf data_conf asm_conf max_heap bitmaps (prog:((num, ('a stackLang$prog)) alist)) =
   (* Compile away GC. *)
   let prog = stack_alloc$compile data_conf prog in
   let prog = stack_remove$compile
               F (* jump? *)
               asm_conf.addr_offset (**)
               T (* gen_gc? *)
               max_heap
               (asm_conf.reg_count - (LENGTH asm_conf.avoid_regs +3))
               InitGlobals_location
               prog
   in
     compile_to_module conf asm_conf bitmaps prog
`

val comply_def = Define `comply bytes ffis = SOME (bytes, [] (* data *), ffis)`

val compile_def = Define `
  compile conf data_conf asm_conf max_heap bitmaps prog =
    let (module, ffis) = compile_without_encoding conf data_conf asm_conf max_heap bitmaps prog in
      comply (enc_module module) ffis`

val _ = export_theory()
