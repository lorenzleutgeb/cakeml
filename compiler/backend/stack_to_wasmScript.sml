open preamble stackLangTheory wasmLangTheory

(* NOTE: wasm behaves differently compared to the alternative
 *       branch (stack->lab->target) in that it will encode
 *       to bytes directly. The exporter then does "nothing".
 *       This is to keep compatiblity. *)
open wasm_binaryTheory

local open stack_allocTheory stack_removeTheory stack_namesTheory
           word_to_stackTheory bvl_to_bviTheory in end

val _ = new_theory "stack_to_wasm";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = Datatype `
  config =
    <| heap_sz  : num
     ; stack_sz : num
     |>`

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
    | Ror => Rotr`

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

(* Extracts the names of all foreign functions that instr might call. *)
val extract_ffi_names_def = Define `
  extract_ffi_names = foldl_prog (\p acc.
    case p of
      | FFI name _ _ _ _ _ => name :: acc
      | _                  =>         acc
  ) []`

val reg_to_global_def = Define `reg_to_global n = n2w n`
val fp_reg_to_global_def = Define `fp_reg_to_global n = n2w n (* TODO: Add the number of ordinary registers. *)`

val set_lab_def = Define `set_lab = [Set_global (n2w 42n)]`
val get_lab_def = Define `get_lab = [Get_global (n2w 42n)]`
val set_seg_def = Define `set_seg = [Set_global (n2w 43n)]`
val get_seg_def = Define `get_seg = [Get_global (n2w 43n)]`

val get_reg_def = Define `get_reg r = [Get_global (reg_to_global r)]`
val set_reg_def = Define `set_reg r = [Set_global (reg_to_global r)]`

val get_ri_def = Define `get_ri (Reg r) width = get_reg r /\ get_ri (Imm w) width = [wasmLang$Const (w2val (Tv Ki width) w)]`

val get_fp_reg_def = Define `get_fp_reg r = [Get_global (fp_reg_to_global r)]`
val set_fp_reg_def = Define `set_fp_reg r = [Set_global (fp_reg_to_global r)]`
(* val set_fp_reg_w_def = Define `set_fp_reg_w r v = set_fp_reg r (w2val T_f64 v)` *)

val continue_def = Define `continue n m = [Br (n2w (n + m))]`
val fpop_def = Define `fpop result args op = (FLAT (MAP get_fp_reg args)) ++ op ++ (set_fp_reg result)`
val autowrap_def = Define `autowrap W32 = [] /\ autowrap W64 = [Conversion Wrap]`

(* Function to map basic instructions. The following does not cover all instrs,
 * but only those for which stackSem$inst actually defines a semantics. *)
val _ = Define `
  compile_inst (x:('a inst)) =
    let
      width = wasm_width (:'a);
      rt = Tv Ki width;
      vzro = (w2val rt (0w:'a word));
      vone = (w2val rt (1w:'a word))
    in case x of
      | Skip =>
        [Nop]
      | Const reg (w:'a word) =>
        [Const (w2val (Tv Ki width) w)] ++ (set_reg reg)
      | Arith (Binop bop r1 r2 ri) =>
        (get_reg r2) ++ (get_ri ri width) ++ [Binop_i width (compile_binop bop)] ++ (set_reg r1)
      | Arith (Shift sh r1 r2 n) =>
        (get_reg r2) ++ [wasmLang$Const (w2val rt (n2w n:word32))] ++ [Binop_i width (compile_shift sh)] ++ (set_reg r1)
      | Arith (Div r1 r2 r3) =>
        (get_reg r3) ++ (get_reg r2) ++ [Binop_i width (wasmLang$Div U)] ++ (set_reg r1)
      | Arith (AddCarry r1 r2 r3 r4) =>
        (* First, make sure carry is either one or zero, to avoid surprises. *)
        (*    * stackSem: if c = 0w then 0 else 1 *)
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
  jmp_indirect n m r w =
    (get_reg r) ++ (
      if w = W32
      then [Conversion Wrap]
      else [Const (V_i32 0xFFFFw); Binop_i W32 And]
    ) ++ set_lab ++
    (get_reg r) ++ (
        if w = W32
        then [Const (V_i32 16w); Binop_i W32 (Shr U)]
        else [wasmLang$Const (V_i64 32w); Binop_i W64 (Shr U); Conversion Wrap]
    ) ++ set_seg ++
    continue n m
`

val jmp_def = Define `
  jmp n m n' m' =
    [wasmLang$Const (V_i32 (n2w n'))] ++ set_seg ++
    [wasmLang$Const (V_i32 (n2w m'))] ++ set_lab ++
    (continue n m)
`

val jmp_if_def = Define `jmp_if n m c r ri n' m' = ((compile_cmp c r ri) ++ [wasmLang$If [] (jmp n m n' m') []])`

val compile_jump_def = Define `
(compile_jump n' m' (INL n) w = jmp          n' m' n 0) /\
(compile_jump n' m' (INR r) w = jmp_indirect n' m' r w)`;

val switch_def = Define `
  switch v bs = FOLDR
    (\x acc. Block [] acc::x)
    [Block [] (v ++ [Br_table (to_nlist (GENLIST (\i. n2w (i + 1)) (LENGTH bs))) 0w])]
    bs
`

val lab_def = Define `lab = [Block [] []]`

val simple_if_def = Define `simple_if n m c r ri l1 l2 other =
  ((jmp_if n m c r ri n m) ++ l1 ++ lab ++ l2, other, m + 1)`

val splitall_def = Define `splitall p xs = FOLDR (\x acc. if p x then CONS [] acc else (CONS (CONS x (HD acc)) (TL acc))) [] xs`
val lab2reg_def = Define `lab2reg i l1 l2 = [(wasmLang$Const (V_i64 (word_or (word_lsl (n2w l1) 32) (n2w l2))))] ++ (set_reg i)`

(* Go from top to bottom, and when a new lab is requested: Generate a new Block, put the *)
(* own code afterwards and recurse into the block. *)
local val compile_section_quotation = `
  compile_section (p:'a stackLang$prog) n m =
    let width = wasm_width (:'a) in dtcase p of
    | Tick => ([Nop], F, m)
    | Inst a => (compile_inst a, F, m)
    | Halt _ => ([], T, m) (* TODO: Set some flag that will stop execution. *)

    | Seq p1 p2 =>
        let (l1, nr1, m) = compile_section p1 n m ;
            (l2, nr2, m) = compile_section p2 n m in
            (l1 ++ l2, nr1 \/ nr2, m)

    | stackLang$If c r ri p1   p2   =>
          if p1 = Skip /\ p2 = Skip then ([], F, m) else
          if p1 = Skip then let (l2, nr2, m) = compile_section p2 n m in simple_if n m       c  r ri l2 [] F else
          if p2 = Skip then let (l1, nr1, m) = compile_section p1 n m in simple_if n m (flip c) r ri l1 [] F else
          let (l1, nr1, m) = compile_section p1 n m ;
              (l2, nr2, m) = compile_section p2 n m in
                   if nr1 then simple_if n m (flip c) r ri l1 l2 nr2
              else if nr2 then simple_if n m       c  r ri l2 l1 nr1
              else
                  ((jmp_if n m c r ri n  m     )        ++ l2 ++
                   (jmp    n m        n (m + 1)) ++ lab ++ l1 ++ lab, F, m + 2)

    | While c r ri p =>
        let (l, _, m) = compile_section p n m in
            (lab ++ (jmp_if n m (flip c) r ri n (m + 1)) ++ l
                 ++ (jmp    n m               n  m     ) ++ lab, F, m + 2)

    | Raise  r   => (jmp_indirect n m r width, T, m)
    | Return r _ => (jmp_indirect n m r width, T, m)
    | JumpLower r1 r2 target => (jmp_if n m Lower r1 ((Reg r2):'a reg_imm) target 0, F, m)

    | stackLang$Call  NONE                          dest _  => (compile_jump n m dest width, T, m)
    | stackLang$Call (SOME (rhp, rhlr, rhl1, rhl2)) dest eh =>
        let (rhi, nr1, m) = compile_section rhp n m ;
            prefix = (lab2reg rhlr rhl1 rhl2) ++ (compile_jump n m dest width) ++ lab ++ rhi in
        (dtcase eh of
        | NONE => (prefix, nr1, m)
        | SOME (ehp, ehl1, ehl2) =>
          let (ehi, nr2, m) = compile_section ehp n m in
              (prefix ++ (jmp n m n m) ++ lab ++ ehi ++ lab, nr1 /\ nr2, m + 1))

    | FFI ffi_index ptr1 len1 ptr2 len2 _ =>
          ([
            (Const (V_i32 (n2w ptr1)));
            (Const (V_i32 (n2w len1)));
            (Const (V_i32 (n2w ptr2)));
            (Const (V_i32 (n2w len2)));
            (Call (0w:funcidx) (* TODO: Find out how to get the correct funcidx! *))
          ], F, n)
        (* Since we must use wasm's Call instruction here, we do not emit a new lab, *)
        (*      * do not deal with the link register, etc. *)
        (*      * NOTE: We actually do not use the link register even though it was allocated... *)

    | LocValue i l1 l2 => ((lab2reg i l1 l2), F, m)

    (* NOTE: Install and CodeBufferWrite are left out in the initial implementation. *)
    | _  => ([], F, m)
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

val segment_to_block_def = Define `
  segment_to_block (n, p) =
    let (lines, _, m) = (compile_section p n (next_lab p 1)) in
      switch (get_lab) (splitall (\x. x = (Block [] [])) (lab ++ lines))
`

val build_body_def = Define `
  build_body (bs: ((wasmLang$instr list) list)) =
    switch (get_seg) bs`

val w2bs_def = Define `w2bs w = (MAP n2w (word_to_oct_list w)):(byte list)`
val ws2bs_def = Define `ws2bs = FLAT o MAP w2bs`
val str2bs_def = Define `str2bs = MAP (\c. n2w_itself (ORD c, (:8)))`

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
    let mem = <| type := <| min := size; max := SOME size |> |> in
    let offset = n2w_itself (heapnstack * page_size, (:32)) in
    let bitmap_mark = <| data := 0w ; offset := Expr [Const (V_i32     0w)]; init := ws2bs [0w:word32; offset] |> in
    let bitmap_data = <| data := 0w ; offset := Expr [Const (V_i32 offset)]; init := ws2bs bitmaps |> in
    (mem, [bitmap_mark; bitmap_data])`

(* TODO: Use asm_conf.link_reg for br_table madness? *)
val asm_to_globals = Define `
  asm_to_globals conf asm_conf =
    let heap_sz = conf.heap_sz * 1024n * 1024n in
    let stack_sz = conf.stack_sz * 1024n * 1024n in
    let cake_heap = 0n in
    let cake_stack = heap_sz in
    let cake_end = cake_stack + stack_sz in
    [
      (* The first four are special, since they must be initialized. *)
      (* The address of main. *)
      global_zero T_var T_i64;
      (* First heap address. *)
      global_zero T_var T_i64;
      (* First stack address. *)
      <| type := T_global T_var T_i64; init := Expr [Const (V_i64 (n2w cake_stack))] |>;
      (* First address after the stack. *)
      <| type := T_global T_var T_i64; init := Expr [Const (V_i64 (n2w cake_end))] |>;
    ] ++
    (* TODO: Should we subtract LENGTH asm_conf.avoid_regs from asm_conf.reg_count? *)
    (* All other registers. *)
    (GENLIST (\x. global_zero T_var T_i64) (asm_conf.reg_count - 4n)) ++
    (* Floating-Point registers. *)
    (GENLIST (\x. global_zero T_var T_f64) asm_conf.fp_reg_count)
`

val ffi_names_to_imports_def = Define `
  ffi_names_to_imports ffi_type_index =
    MAP (\x. <| module := str2bs "ffi"; name := str2bs x; desc := Import_func ffi_type_index |>)`

val _ = temp_overload_on("main_type", ``Tf [] []``)
val _ = temp_overload_on("ffi_type", ``Tf [T_i32; T_i32; T_i32; T_i32] []``)

val wrap_block_def = Define `
  wrap_block b conf asm_conf ffi_names bitmaps =
    let (mem, data) = create_memory conf bitmaps in
    <| types  := [main_type; ffi_type]
     ; funcs  := [<| type := 0w; locals := []; body := Expr b |>]
     ; tables := []
     ; mems   := [mem]
     ; globals:= (asm_to_globals conf asm_conf)
     ; elem   := []
     ; data   := data
     ; start  := (SOME <| func := 0w |>)
     ; imports:= (ffi_names_to_imports 1w ffi_names)
     ; exports:= [<| name := str2bs "memory"; desc := Export_mem 0w |>;
                  <| name := str2bs "main"  ; desc := Export_func 0w|>]
     |>`

val compile_without_encoding_def = Define `
 compile_without_encoding conf data_conf asm_conf max_heap bitmaps prog =
   let sp = asm_conf.reg_count - (LENGTH asm_conf.avoid_regs +3) in
   let offset = asm_conf.addr_offset in
   (* First, the intermediate translations from stack_to_lab: *)
   let prog = stack_alloc$compile data_conf prog in
   let prog = stack_remove$compile F offset T
                max_heap sp InitGlobals_location prog in
   (* After all intermediates, extract FFI names. It would be
    * more cumbersome to extract them from wasm code. *)
   let ffis = FLAT (MAP extract_ffi_names (MAP SND prog)) in
   (* Now, towards wasm. *)
   let seg_blocks = MAP segment_to_block prog in
   let body = build_body seg_blocks in
       wrap_block body conf asm_conf ffis bitmaps`;

(* We report no data and no FFI names, since we encode them into the first element. *)
val comply_def = Define `comply x = SOME (x, [], [])`

val compile_def = Define `
  compile conf data_conf asm_conf max_heap bitmaps prog =
    let module = compile_without_encoding conf data_conf asm_conf max_heap bitmaps prog in
      comply (enc_module module)`

val _ = export_theory()
