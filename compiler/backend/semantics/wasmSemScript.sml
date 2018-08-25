(* NOTE: This theory is based on
 *
 *  WebAssembly Core Specification
 *  W3C First Public Working Draft, 15 February 2018
 *
 * which is available at
 *
 *  https://w3.org/tr/2018/wd-wasm-core-1-20180215/
 *
 * At the time of writing (August 2018), the version
 * above is not significantly outdated. To compare
 * against the most current version, see
 *
 *  https://github.com/webassembly/spec/compare/fpwd...master
 *
 * The ordering of definitions is meant to mirror the
 * original document. However, some exceptions were
 * made to have all definitions "straight forward".
 * These exceptions are marked with comments.
 *
 * This theory contains definitions used by both the small-step as well
 * as the functional big-step semantics for wasm. *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmLangTheory patternMatchesLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES()

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmSem"

(* 4.2  Runtime Structure *)

(* 4.2.2  Results *)
(* NOTE: The spec currently says that this list can have at most one
 *       element. However it notes that this restriction might be lifted
 *       in the future.
 *       The issue that tracks multi-value returns is at
 *        https://github.com/WebAssembly/design/issues/1146
 *)
val _ = type_abbrev("result", ``:val list``)

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

(* 4.2.6  Function Instances *)

(* NOTE: Host Functions are not explicitly defined in the spec. We use them
 *       as a vehicle to index a collection of host functions that live
 *       outside the wasm store. The actual host function is then able to
 *       consume the wasm store and create a new one (conforming with the
 *       constraints on host functions mentioned in section 4.4.7.3 and
 *       formalized in section 7.5.2.3.
 *)
val _ = type_abbrev("hostfunc", ``:string``)

val _ = Datatype `
funcinst =
   (* <| type: functype; module: moduleinst; code: func |> *)
   | Native functype moduleinst func
   (* <| type: functype; hostcode hostfunc |> *)
   | Host   functype hostfunc`

val funcinst_type_def = Define `funcinst_type (Native tf mi f) = tf /\ funcinst_type (Host tf hf) = tf`

(* 4.2.7  Table Instances *)
val _ = type_abbrev("funcelem", ``:(funcaddr option)``)
val _ = Datatype `tableinst = <| elem: funcelem list; max: u32 |>`

(* 4.2.8  Memory Instances *)
val _ = Datatype `meminst = <| data: byte vec; max: u32 |>`
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

(* TODO: 4.2.11.1  Conventions *)

(* 4.2.12.3  Frames *)
(* Moved up since instr depends on frame. *)
val _ = Datatype `frame = <| locals: val list; module: moduleinst |>`

(* 4.2.12.2  Labels *)
(* There is no necessity for a separate label type. *)
(* val _ = Datatype `label = T_Label num (instr list)` *)

(* 4.2.12.3  Frames *)
(* Definition of frame was moved to wasmLang. *)
val _ = Datatype `activation = Activation num frame`

(* 4.2.13  Administrative Instructions *)
val _ = Datatype `
  ainstr =
    | Plain instr
    | Trap
    | Invoke funcaddr
    | Init_elem tableaddr u32 (funcidx list)
    | Init_data memaddr u32 (byte list)
    | Label num (instr list) (instr list)
    | Frame num frame (instr list)`

(* 4.2.13.1  Block Contexts *)
(* Parameters of the constructors x are indicated as <x>. *)
val _ = Datatype `
  block =
(* B^0 ::= <val*> [_] <instr*> *)
    | B0 result (ainstr list)
(* B^(k+1) ::= <val*> label_<n> { <ainstr*> } B^k end <instr*> *)
    | Bk result num (ainstr list) block (ainstr list)`

val fill_b_def = Define `
fill_b 0n (B0 vs is)          filler = MAP Const vs ++ filler ++ is /\
fill_b k  (Bk vs n i1s b i2s) filler = MAP Const vs ++ [Label n i1s (fill_b (k - 1n) b filler)] ++ i2s`

(* 4.2.13.2  Configurations *)
val _ = Datatype `thread = Thread frame result (ainstr list)`
val _ = Datatype `config = Config store thread`

(* The above definitions of threads and configs from the spec is
 * a bit heavy. We introduce triples as a shorthand notation, as
 * used in the spec.
 *)
val _ = type_abbrev("configuration", ``:(store # frame # (result # (ainstr list)))``)

(* To model host functions that mutate the store, we wrap the
 * confugiration once again into a structure that references host functions.
 * Over this structure we can model what happens when a host function is
 * invoked. The small step semantics in the wasm specification is simply
 * lifted to this case.
 *)
val _ = type_abbrev("hostfuncimpl", ``:store -> result -> (store # result)``)

(* FFI Calls: A hostfunc is a string, which just names the foreign function.
 * This string is passed to call_ffi and further to the oracle.

 * Oracle operations need to be wrapped a bit.
 * The two input parameters (both of type (word8 list)) are to be passed via the stack,
 * just as with a normal invocation, this is specified in 4.4.7.3. However, we need to
 * fix a representation of an array. In other languages (wordLang and stackLang) this
 * is done by specifying an address (pointer) and the length.
 * This would mean that any foreign function in our setting would have a wasm function
 * type of:
 *             ptr1   len1   ptr2   len2
 *   consumes [T_i32; T_i32; T_i32; T_i32]
 *
 * Note that the second memory region is modified in place, i.e. the wrapping code must
 * store the result obtained from the oracle in the memory at addres ptr2.
 *)

(* For integration with CakeML we define a state which subsumes a configuration,
 * since it contains a store and the the (intermediate) result and stack of the
 * only thread.
 * Once threads become available in WebAssembly, see
 *  https://github.com/WebAssembly/threads
 * one may want to add this indirection here by moving frame, result and stack
 * into a separate collection, and adding events. C.f. also the datatype config. *)
val _ = Datatype `
  state =
    <| ffi: 'ffi ffi_state
     ; store: store
     ; result: result
     ; frame: frame
     ; stack: (ainstr list)
     ; clock: num
     |>`

val mk_config_def = Define `mk_config (s, f, is) = Config s (Thread f is)`

(* 4.2.13.3  Evaluation Context *)
val _ = Datatype `
  e =
(* [_] *)
    | E0
(* <val*> <E> <instr*> *)
    | Ex result e (ainstr list)
(* label_<n> { <instr*> } <E> end *)
    | Ey num (ainstr list) e`

val fill_e_def = Define `
fill_e E0           filler = filler /\
fill_e (Ex vs e is) filler = MAP Const vs ++ fill_e e filler ++ is /\
fill_e (Ey n is e)  filler = [Label n is (fill_e e filler)]`

(* 4.3  Numerics *)
(* 4.3.2  Integer Operations *)
(* NOTE: ctz = count trailing zeros, clz = count leading zeros, popcnt = count 1s *)
val _ = Define `app_unop_i Ctz c = 0w /\ app_unop_i Clz c = 0w /\ app_unop_i Popcnt c = 0w`

val _ = Define
  `app_binop_i iop c1 c2 = SOME (case iop of
                              Add => word_add c1 c2
                            | Sub => word_sub c1 c2
                            | Mul => word_mul c1 c2
                            | Div U => word_div c1 c2
                            | Div S => word_sdiv c1 c2
                            | Rem U => word_mod c1 c2
                            | Rem S => word_smod c1 c2
                            | And => word_and c1 c2
                            | Or => word_or c1 c2
                            | Xor => word_xor c1 c2
                            | Shl => word_lsl c1 (w2n c2)
                            | Shr U => word_lsr c1 (w2n c2)
                            | Shr S => word_asr c1 (w2n c2)
                            | Rotl => word_rol c1 (w2n c2)
                            | Rotr => word_ror c1 (w2n c2))`

val _ = Define `app_testop_i Eqz c = (w2n c = 0)`

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

val _ = Define
  `app_binop_f fop c1 c2 = (case fop of
                              Addf => SOME (SND (float_add roundTiesToEven c1 c2))
                            | Subf => SOME (SND (float_sub roundTiesToEven c1 c2))
                            | Mulf => SOME (SND (float_mul roundTiesToEven c1 c2))
                            | Divf => SOME (SND (float_div roundTiesToEven c1 c2))
                            | Min => SOME (if float_greater_equal c1 c2 then c2 else c1)
                            | Max => SOME (if float_greater_equal c1 c2 then c1 else c2)
                            | Copysign => SOME (if c1.Sign = c2.Sign then c1 else (float_negate c1)))`

val _ = Define
  `app_relop_f rop c1 c2 = (case rop of
                              Eqf => float_equal c1 c2
                            | Nef => ~float_equal c1 c2
                            | Ltf => float_less_than c1 c2
                            | Gtf => float_greater_than c1 c2
                            | Lef => float_less_equal c1 c2
                            | Gef => float_greater_equal c1 c2)`

(* 4.3.4  Conversions *)

val bytes2word_def = Define `bytes2word (bs:byte list) = l2w 8n (MAP w2n bs)`
val word2bytes_def = Define `word2bytes w = (MAP n2w (w2l 8n w)):(byte list)`

val bytes2val_def = Define `
(bytes2val T_i32 = V_i32 o bytes2word) /\
(bytes2val T_i64 = V_i64 o bytes2word) /\
(bytes2val T_f32 = V_f32 o (\ (w:word32). <| Sign := (0 >< 0) w; Exponent := ( 8 >< 1) w; Significand := (31 ><  9) w |>) o bytes2word) /\
(bytes2val T_f64 = V_f64 o (\ (w:word64). <| Sign := (0 >< 0) w; Exponent := (11 >< 1) w; Significand := (63 >< 12) w |>) o bytes2word)`

val val2bytes_def = Define `
(val2bytes (V_i32 v) = word2bytes v) /\
(val2bytes (V_i64 v) = word2bytes v) /\
(val2bytes (V_f32 v) = word2bytes (word_join v.Significand (word_join v.Exponent v.Significand))) /\
(val2bytes (V_f64 v) = word2bytes (word_join v.Significand (word_join v.Exponent v.Significand)))`

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
cvt Demote (V_f64 v) = SOME ((V_f32 o real_to_float roundTiesToEven o float_to_real) v) /\
cvt Promote (V_f32 v) = SOME ((V_f64 o real_to_float  roundTiesToEven o float_to_real) v) /\
cvt (Reinterpret t) v = SOME ((bytes2val (other_kind (typeof v)) o val2bytes) v)
`

(* Some functions that define the semantics of instructions return an option.
 * Generally, if they return NONE, then this corresponds to a trap in wasm.
 * This is a helper, additionally parameterized by some f that we put in
 * between the option check and construction a constant. Usually f will be
 * a constructor of val.
 *)
val wrap_option_def = Define `
wrap_option f (SOME x) = Const (f x) /\
wrap_option f NONE     = Trap`

(* Some functions that define the semantics of instructions return booleans.
 * In wasm, booleans are represented by the two constants i32.const 0 and
 * i32.const 1, which we get by applying this wrapping function.
 *)
val wrap_bool_def = Define `
wrap_bool T = Const (V_i32 1w) /\
wrap_bool F = Const (V_i32 0w)`

val arguments_ok = Define `arguments_ok vs (Tf ts rt) = LIST_REL (\v t. t = typeof v) vs ts`

val zero_def = Define `
zero T_i32 = V_i32 0w /\
zero T_i64 = V_i64 0w /\
zero T_f32 = V_f32 <|Sign := 0w; Exponent := 0w; Significand := 0w|> /\
zero T_f64 = V_f64 <|Sign := 0w; Exponent := 0w; Significand := 0w|>`

val has_def = Define `has xs i x = (i < (LENGTH xs) /\ EL i xs = x)`
val mem0_def = Define `mem0 s f = (EL (HD f.module.memaddrs) s.mems)`

val mem_range = Define `mem_range m i ma n =
  let ea = w2n ((word_add i ma.offset):i32); len = (n DIV 8) in
    if (LENGTH m.data) <= ea + len then NONE
    else                                SOME (ea, len)`

(* Helper to read from a memory instance m, given the index i,
 * the memarg ma and the with n. Returns SOME (byte list) in
 * case the read is within bounds of m or else NONE.
 *)
val mem_read_def = Define `mem_read m i ma n =
  OPTION_MAP (\ (ea, n). (GENLIST (\i. EL (ea + i) m.data) n)) (mem_range m i ma n)
`

val mem_write_def = Define `mem_write m i ma n v =
  OPTION_MAP (\ (ea, n). (GENLIST (\i. if i < ea \/ ea + n < i then EL i m.data else EL (i - ea) (val2bytes v)) (LENGTH m.data)))
`

val consts_def = Define `consts v = MAP (Const o v)`

val _ = export_theory()
