(* NOTE: This theory is based on
 *
 *  WebAssembly Core Specification
 *  W3C First Public Working Draft, 4 September 2018
 *
 * which is available at
 *
 *  https://w3.org/tr/2018/wd-wasm-core-1-20180904
 *
 * At the time of writing (September 2018), the version
 * above is not significantly outdated. To compare
 * against the most current version, see
 *
 *  https://github.com/webassembly/spec
 *
 * The ordering of definitions is meant to mirror the
 * original document. However, some exceptions were
 * made to have all definitions "straight forward".
 * These exceptions are marked with comments.
 *
 * This theory contains definitions used by both the
 * small-step as well as the functional big-step
 * semantics for wasm. *)

open preamble wasmLangTheory

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()
val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSemanticPrimitives"

(* 4.2  Runtime Structure *)
(* 4.2.4  Addresses *)
(* https://www.w3.org/TR/2018/WD-wasm-core-1-20180215/#addresses%E2%91%A0 *)
(* Moved up since externval needs addrs. *)
val _ = type_abbrev(      "addr", ``:num``)
val _ = type_abbrev(  "funcaddr", ``:addr``)
val _ = type_abbrev( "tableaddr", ``:addr``)
val _ = type_abbrev(   "memaddr", ``:addr``)
val _ = type_abbrev("globaladdr", ``:addr``)

(* 4.2.11  External Values *)
val _ = Datatype `
  externval =
    | Func     funcaddr
    | Table   tableaddr
    | Mem       memaddr
    | Global globaladdr`

(* 4.2.11.1  Conventions *)
val _ = Define `externval_funcs   = FOLDR (\x l. case x of Func   y => y::l | _ => l) []`
val _ = Define `externval_tables  = FOLDR (\x l. case x of Table  y => y::l | _ => l) []`
val _ = Define `externval_mems    = FOLDR (\x l. case x of Mem    y => y::l | _ => l) []`
val _ = Define `externval_globals = FOLDR (\x l. case x of Global y => y::l | _ => l) []`

(* 4.2.10  Export Instances *)
val _ = Datatype `exportinst = <| name: name; value: externval |>`

(* 4.2.5  Module Instances *)
val _ = Datatype `moduleinst =
 <| types      :   functype list
  ; funcaddrs  :   funcaddr list
  ; tableaddrs :  tableaddr list
  ; memaddrs   :    memaddr list
  ; globaladdrs: globaladdr list
  ; exports    : exportinst list
  |>`

val moduleinst_empty_def = Define `moduleinst_empty =
  <| types      := []
   ; funcaddrs  := []
   ; tableaddrs := []
   ; memaddrs   := []
   ; globaladdrs:= []
   ; exports    := []
   |>
`

(* 4.2.6  Function Instances
 *
 * For CakeML, we introduce host functions that refer to foreign functions.
 *
 * The two input parameters (both of type (word8 list)) are to be passed via the stack,
 * just as with a normal invocation, this is specified in 4.4.7.3. However, we need to
 * fix a representation of an array. In other languages (wordLang and stackLang) this
 * is done by specifying an address (pointer) and the length.
 * This implies that any host function in our setting has a function type of:
 *
 *             ptr1   len1   ptr2   len2
 *   consumes [T_i32; T_i32; T_i32; T_i32]
 *
 * The second memory region is modified in place.
 *)

val _ = Datatype `
  hostfunc = ForeignFunction string`

val _ = Datatype `
  funcinst =
    | Native functype moduleinst func
    | Host   hostfunc`

val funcinst_type_def = Define `
funcinst_type (Native tf m f)            = tf /\
funcinst_type (Host (ForeignFunction s)) = ffi_type`

(* 4.2.7  Table Instances *)
val _ = type_abbrev("funcelem", ``:(funcaddr option)``)
val _ = Datatype `tableinst = <| elem: funcelem list; max: u32 option |>`

(* 4.2.8  Memory Instances *)
val _ = Datatype `meminst = <| data: byte vec; max: u32 option |>`
val _ = Define `page_size = 65536n`
val _ = Define `bytes_to_pages x = x DIV page_size`

(* 4.2.9  Global Instances *)
val _ = Datatype `globalinst = <| value: val; mut: mut |>`

(* 4.2.3  Store *)
val _ = Datatype `store =
  <| funcs  :   funcinst list
   ; tables :  tableinst list
   ; mems   :    meminst list
   ; globals: globalinst list
   |>`

val store_empty_def = Define `store_empty =
  ((<| funcs  := []
   ; tables := []
   ; mems   := []
   ; globals:= []
   |>): store)`

(* 4.2.12.3  Frames *)
val _ = Datatype `frame = <| locals: val list; module: moduleinst |>`

val _ = overload_on("frame_empty", ``<| locals := []; module := moduleinst_empty |>``)

(* 4.2.13  Administrative Instructions *)

(* NOTE: The spec also defines a Trap instruction, which is missing
 * here and handled as a separate result of the semantics. *)
val _ = Datatype `
  ainstr =
    | Plain instr

    | Invoke funcaddr

    | Init_elem tableaddr u32 (funcidx list)
    | Init_data   memaddr u32 (   byte list)

    | Label num (instr list) ((val list) # (ainstr list))
    | Frame num frame        ((val list) # (ainstr list))

    (* For functional semantics. *)
    | Breaking   num  (val list) (* c.f. fill_b *)
    | Returning (*1*) (val list) (* c.f. fill_e *)
`

val _ = type_abbrev("code", ``:((val list) # (ainstr list))``)

val push_code_def = Define `push_code (vs1, es1) (vs2, es2) = ((vs2 ++ vs1), (es2 ++ es1))`

(* 4.2.13.1  Block Contexts *)
(* Parameters of the constructors x are indicated as <x>. *)
val _ = Datatype `
  block =
(* B^0 ::= <val*> [_] <instr*> *)
    | B0 code
(* B^(k+1) ::= <val*> label_<n> { <ainstr*> } B^k end <instr*> *)
    | Bk (val list) num (instr list) block (ainstr list)`

val fill_b_def = Define `
fill_b (B0 c)              filler = push_code c filler /\
fill_b (Bk vs n i1s b i2s) filler = (vs, ([Label n i1s (fill_b b filler)] ++ i2s))`

val b_depth_def = Define `
b_depth (B0 c) = 0n /\
b_depth (Bk vs n i1s b i2s) = (b_depth b) + 1n`

(* 4.2.13.2  Configurations *)
val _ = Datatype `thread = Thread frame code`
val _ = Datatype `config = Config store thread`

(* 4.2.13.3  Evaluation Context *)
val _ = Datatype `
  e =
    (* [_] *)
    | E0
    (* <val*> <E> <instr*> *)
    | Ex (val list)       e (ainstr list)
    (* label_<n> { <instr*> } <E> end *)
    | Ey num (instr list) e`

val fill_e_def = Define `
fill_e  E0            filler = filler /\
fill_e (Ex   vs e es) filler = push_code (vs, es) (fill_e e filler) /\
fill_e (Ey n es e   ) filler = ([], [Label n es (fill_e e filler)])`

(* 4.3  Numerics *)
(* 4.3.2  Integer Operations *)
(* NOTE: ctz = count trailing zeros, clz = count leading zeros, popcnt = count 1s *)
val _ = Define `
app_unop_i Clz    (w:'a word) = n2w_itself (if w = 0w then dimindex (:'a) else dimindex (:'a) - 1 - LOG2 (w2n w), (:'a)) /\
app_unop_i Ctz    (w:'a word) = n2w_itself (if w = 0w then dimindex (:'a) else LOWEST_SET_BIT            (w2n w), (:'a)) /\
app_unop_i Popcnt (w:'a word) = n2w_itself (bit_count w, (:'a))`

val _ = Define `
  app_binop_i iop c1 c2 = SOME (case iop of
    | Add => word_add c1 c2
    | Sub => word_sub c1 c2
    | Mul => word_mul c1 c2
    | Div U => word_div c1 c2
    | Div S => word_sdiv c1 c2
    | Rem U => word_mod c1 c2
    | Rem S => word_smod c1 c2
    | And => word_and c1 c2
    | Or  => word_or c1 c2
    | Xor => word_xor c1 c2
    | Shl   => word_lsl c1 (w2n c2)
    | Shr U => word_lsr c1 (w2n c2)
    | Shr S => word_asr c1 (w2n c2)
    | Rotl => word_rol c1 (w2n c2)
    | Rotr => word_ror c1 (w2n c2)
  )`

val _ = Define `app_testop_i Eqz c = (c = 0w)`

val _ = Define `
app_relop_i  Eq    a b = (a = b)          /\
app_relop_i  Ne    a b = (a <> b)         /\
app_relop_i (Lt U) a b = word_lt a b      /\
app_relop_i (Lt S) a b = (w2i a < w2i b)  /\
app_relop_i (Gt U) a b = word_gt a b      /\
app_relop_i (Gt S) a b = (w2i a > w2i b)  /\
app_relop_i (Le U) a b = word_le a b      /\
app_relop_i (Le S) a b = (w2i a <= w2i b) /\
app_relop_i (Ge U) a b = word_ge a b      /\
app_relop_i (Ge S) a b = (w2i a >= w2i b)`

(* 4.3.3  Floating-Point Operations *)
(* NOTE: flags are ignored, as hinted in
 *       https://webassembly.github.io/spec/core/exec/numerics.html#floating-point-operations
 *)
val _ = Define `
app_unop_f Negf = float_negate /\
app_unop_f Absf = float_abs /\
app_unop_f Ceilf = round roundTowardPositive o float_to_real /\
app_unop_f Floorf = round roundTowardNegative o float_to_real /\
app_unop_f Truncf = round roundTowardZero o float_to_real /\
app_unop_f Nearestf = round roundTiesToEven o float_to_real /\
app_unop_f Sqrtf c = SND (float_sqrt roundTiesToEven c)`

val float_min_def = Define `float_min x y = if float_greater_equal x y then y else x`
val float_max_def = Define `float_max x y = if float_greater_equal x y then x else y`
val float_copysign = Define `float_copysign x y =(if x.Sign = y.Sign then x else (float_negate x))`

val _ = Define `
  app_binop_f fop x y = SOME (case fop of
    | Addf => SND (float_add roundTiesToEven x y)
    | Subf => SND (float_sub roundTiesToEven x y)
    | Mulf => SND (float_mul roundTiesToEven x y)
    | Divf => SND (float_div roundTiesToEven x y)
    | Min => float_min x y
    | Max => float_max x y
    | Copysign => float_copysign x y
  )`

val float_unequal_def = Define `float_unequal x y = ~float_equal x y`

val _ = Define `
  app_relop_f rop = (case rop of
    | Eqf => float_equal
    | Nef => float_unequal
    | Ltf => float_less_than
    | Gtf => float_greater_than
    | Lef => float_less_equal
    | Gef => float_greater_equal
  )`

(* 4.3.4  Conversions *)

val bs2w_def = Define `bs2w bs = l2w 8n (MAP w2n bs)`
val w2bs_def = Define `w2bs w = (MAP n2w (word_to_oct_list w)):(byte list)`

(* These two variants will guess the width. *)
val w2ival_def = Define `w2ival (w:'a word) = w2val (Tv Ki (wasm_width (:'a))) w`
val w2fval_def = Define `w2fval (w:'a word) = w2val (Tv Kf (wasm_width (:'a))) w`

val int_bounds_def = Define `int_bounds t U = (0i, &(2 EXP (bit_width t)):int) /\ int_bounds t S = (~&(2 EXP ((bit_width t) - 1)), &(bit_width t) - 1)`
val between_def = Define `between (lower:int) (upper:int) (x:int) = (lower <= x /\ x < upper)`
val trunc_def = Define `trunc f t sx = case float_to_int roundTowardZero f of NONE => NONE | SOME x => if (UNCURRY between) (int_bounds t sx) x then SOME (i2w x) else NONE`

(* this function implements all cvtops. *)
val cvt_def = Define `
cvt (Extend S) (V_i32 v) = SOME (V_i64 (i2w (w2i v))) /\
cvt (Trunc W32 sx W32) (V_f32 v) = OPTION_MAP V_i32 (trunc v T_i32 sx) /\
cvt (Trunc W64 sx W32) (V_f32 v) = OPTION_MAP V_i64 (trunc v T_i64 sx) /\
cvt (Trunc W64 sx W64) (V_f64 v) = OPTION_MAP V_i64 (trunc v T_i64 sx) /\
cvt (Trunc W32 sx W64) (V_f64 v) = OPTION_MAP V_i32 (trunc v T_i32 sx) /\
(* Conversions from i32 to f{32,64} *)
cvt (Convert W32 U W32) (V_i32 v) = SOME ((V_f32 o real_to_float roundTiesToEven o real_of_num o w2n) v) /\
cvt (Convert W64 U W32) (V_i32 v) = SOME ((V_f64 o real_to_float roundTiesToEven o real_of_num o w2n) v) /\
cvt (Convert W32 S W32) (V_i32 v) = SOME ((V_f32 o real_to_float roundTiesToEven o real_of_int o w2i) v) /\
cvt (Convert W64 S W32) (V_i32 v) = SOME ((V_f64 o real_to_float roundTiesToEven o real_of_int o w2i) v) /\
(* Conversions from i64 to f{32,64} *)
cvt (Convert W32 U W64) (V_i64 v) = SOME ((V_f32 o real_to_float roundTiesToEven o real_of_num o w2n) v) /\
cvt (Convert W64 U W64) (V_i64 v) = SOME ((V_f64 o real_to_float roundTiesToEven o real_of_num o w2n) v) /\
cvt (Convert W32 S W64) (V_i64 v) = SOME ((V_f32 o real_to_float roundTiesToEven o real_of_int o w2i) v) /\
cvt (Convert W64 S W64) (V_i64 v) = SOME ((V_f64 o real_to_float roundTiesToEven o real_of_int o w2i) v) /\
cvt Demote (V_f64 v) = SOME (w2val T_f32 (fp64_to_fp32 roundTiesToEven (float_to_fp64 v))) /\
cvt Promote (V_f32 v) = SOME ((w2val T_f64 (fp32_to_fp64 (float_to_fp32 v)))) /\
cvt (Reinterpret t) (V_f32 v) = SOME (w2val T_i32 (float_to_fp32 v)) /\
cvt (Reinterpret t) (V_f64 v) = SOME (w2val T_i64 (float_to_fp64 v)) /\
cvt (Reinterpret t) (V_i32 v) = SOME (V_f32 (fp32_to_float v)) /\
cvt (Reinterpret t) (V_i64 v) = SOME (V_f64 (fp64_to_float v))
`

(* Some functions that define the semantics of instructions return booleans.
 * In wasm, booleans are represented by the two constants i32.const 0 and
 * i32.const 1, which we get by applying this wrapping function.
 *)
val wrap_bool = Define `wrap_bool T = V_i32 1w /\ wrap_bool F = V_i32 0w`

val wraps_false_def = Define `
wraps_false v = case v of (V_i32 0w) => T | _ => F`

val arguments_ok = Define `arguments_ok vs (Tf ts rt) = LIST_REL (\v t. t = typeof v) vs ts`

val zero_def = Define `
zero (Tv Ki W32) = V_i32 0w /\
zero (Tv Ki W64) = V_i64 0w /\
zero (Tv Kf W32) = V_f32 (fp32_to_float 0w) /\
zero (Tv Kf W64) = V_f64 (fp64_to_float 0w)`

val has_def = Define `has xs i x = (i < (LENGTH xs) /\ EL i xs = x)`

(* These are handy as long as there is only one mem/table. *)
val memaddr_def = Define `memaddr f = HD f.module.memaddrs`
val get_mem_def = Define `get_mem s f = (EL (memaddr f) s.mems).data`
val set_mem_def = Define `set_mem s f m = let a = memaddr f in s with mems := LUPDATE ((EL a s.mems) with data := m) a s.mems`
val tableaddr_def = Define `tableaddr f = HD f.module.tableaddrs`
val get_table_def = Define `get_table s f = (EL (tableaddr f) s.tables).elem`

val IF_SOME_def = Define `IF_SOME T x = SOME x /\ IF_SOME F x = NONE`
val LUPDATE_MAP_def = Define `LUPDATE_MAP f n l = LUPDATE (f (EL n l)) n l`

val read_mem_def = Define `
  read_mem s f ptr len = let m = get_mem s f in IF_SOME (LENGTH m < ptr + len) (TAKE len (DROP ptr m))`

val write_mem_def = Define `
  write_mem s f ptr bs = let m = get_mem s f; len = LENGTH bs in IF_SOME (LENGTH m < ptr + len)
    (s with mems := LUPDATE_MAP (\m0. m0 with data := (TAKE ptr m) ++ bs ++ (DROP (ptr + len) m)) (memaddr f) s.mems)`

(* NOTE: memarg.align does not affect the semantics, see note at 4.4.4. *)
val mem_range = Define `mem_range i ma n = ((w2n i) + (w2n ma.offset), n DIV 8)`

val mem_load_def = Define `mem_load s f n ma (V_i32 i) = let (ptr, len) = mem_range i ma n in read_mem s f len ptr`

val mem_load_t_n_def = Define `
mem_load_t_n s f (Tv Ki W32) n ma i = OPTION_MAP (V_i32 o bs2w) (mem_load s f n ma i) /\
mem_load_t_n s f (Tv Ki W64) n ma i = OPTION_MAP (V_i64 o bs2w) (mem_load s f n ma i) /\
mem_load_t_n s f (Tv Kf W32) n ma i = OPTION_MAP (V_f32 o fp32_to_float o bs2w) (mem_load s f n ma i) /\
mem_load_t_n s f (Tv Kf W64) n ma i = OPTION_MAP (V_f64 o fp64_to_float o bs2w) (mem_load s f n ma i)
`

val mem_load_t_def = Define `mem_load_t s f t ma i = mem_load_t_n s f t (bit_width t) ma i`

val mem_load_sz_sx_def = Define `
mem_load_sz_sx s f w tp U ma i = mem_load_t_n s f (Tv Ki w) (bit_width_p tp) ma i /\
mem_load_sz_sx s f W32 S8 S ma i = OPTION_MAP (\x.((V_i32 o i2w o w2i) ((bs2w x):word8))) (mem_load s f 8 ma i) /\
mem_load_sz_sx s f W32 S16 S ma i = OPTION_MAP (\x.((V_i32 o i2w o w2i) ((bs2w x):word16))) (mem_load s f 16 ma i) /\
mem_load_sz_sx s f W32 S32 S ma i = OPTION_MAP (\x.((V_i32 o i2w o w2i) ((bs2w x):word32))) (mem_load s f 32 ma i) /\
mem_load_sz_sx s f W64 S8 S ma i = OPTION_MAP (\x.((V_i64 o i2w o w2i) ((bs2w x):word8))) (mem_load s f 8 ma i) /\
mem_load_sz_sx s f W64 S16 S ma i = OPTION_MAP (\x.((V_i64 o i2w o w2i) ((bs2w x):word16))) (mem_load s f 16 ma i) /\
mem_load_sz_sx s f W64 S32 S ma i = OPTION_MAP (\x.((V_i64 o i2w o w2i) ((bs2w x):word32))) (mem_load s f 32 ma i)
`

val mem_store_def = Define `mem_store s f n ma (V_i32 i) w = let (ptr, len) = mem_range i ma n in (write_mem s f ptr (w2bs w))`

(* Variant of mem_store that will infer the correct length based on the type of the given value. *)
val mem_store_t_def = Define `
mem_store_t s f ma i (V_i32 v) = mem_store s f 32 ma i v /\
mem_store_t s f ma i (V_i64 v) = mem_store s f 64 ma i v /\
mem_store_t s f ma i (V_f32 v) = mem_store s f 32 ma i (float_to_fp32 v) /\
mem_store_t s f ma i (V_f64 v) = mem_store s f 64 ma i (float_to_fp64 v)
`

(* Variant of mem_store that accounts for a storage size. *)
val mem_store_sz_def = Define `
mem_store_sz s f S8  ma i (V_i32 v) = mem_store s f  8 ma i (w2w v: ( 8 word)) /\
mem_store_sz s f S16 ma i (V_i32 v) = mem_store s f 16 ma i (w2w v: (16 word)) /\
mem_store_sz s f S32 ma i (V_i32 v) = mem_store s f 32 ma i (w2w v: (32 word)) /\
mem_store_sz s f S8  ma i (V_i64 v) = mem_store s f  8 ma i (w2w v: ( 8 word)) /\
mem_store_sz s f S16 ma i (V_i64 v) = mem_store s f 16 ma i (w2w v: (16 word)) /\
mem_store_sz s f S32 ma i (V_i64 v) = mem_store s f 32 ma i (w2w v: (32 word))
`

(* Results are the same for both semantics. *)
val _ = Datatype `
  result =
    (* NOTE: The spec currently says that this list can have at most one
     *       element. However it notes that this restriction might be lifted
     *       in the future.
     *       The issue that tracks multi-value returns is at
     *        https://github.com/WebAssembly/design/issues/1146
     *       See also 4.4.2
     *)
    | Result (val option)
    (* If execution raises a trap, with some message describing the reason. *)
    | Trap string
    (* If a the instance is found to violate validity. *)
    | TypeError string
    | Timeout
    | FinalFFI final_event`

val wrap_result_def = Define `
  wrap_result l = if LENGTH l <= 1
                  then Result (oHD l)
                  else TypeError "Expected result of at most one value"
`

val wrap_result_eq_result = Q.store_thm("wrap_result_eq_result[simp]",
  `LENGTH l < 2 ==> wrap_result l = Result (oHD l)`,
  rw [wrap_result_def]
)

val _ = export_theory()
