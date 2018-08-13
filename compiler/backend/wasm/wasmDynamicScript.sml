(* NOTE: Please consult README.md *)

open HolKernel boolLib Parse bossLib wordsTheory binary_ieeeTheory integer_wordLib arithmeticTheory wasmLangTheory

val _ = ParseExtras.tight_equality()

val _ = new_theory "wasmDynamic"

(* 4  Execution *)

(* NOTE: We define a number of reduction relations:
 *
 *       (instr list) -s-> (instr list)  (from "simple")
 *       For rules that do not depend on the current store/frame
 *       but only operate on the stack.
 *
 *       configuration ---> configuration
 *       For rules that do depend on the current store/frame.
 *       This relation is the main one from the spec.
 *
 *       environment -c-> environment  (from "complex")
 *       For rules that call host functions, to avoid a
 *       circular dependency between store and hostfunc.
 *
 *       expr -e->  expr  (from "expression")
 *       Similar to -s->.
 *)

(* 4.2  Runtime Structure *)

(* 4.2.2  Results *)
(* NOTE: Stricly, the spec defines the first case as a val list. However, it states
 * that currently a result can consist of at most one value.
 * We model this as an option type:
 *  SOME v  means that the outcome of a computation is v
 *  NONE    means that the the outcome of a computation is a trap
 * The issue that tracks multi-value returns is at
 *   https://github.com/WebAssembly/design/issues/1146
 *)
val _ = type_abbrev("result", ``:val option``)

val mk_result_def = Define `mk_result [Const v] = SOME v /\ mk_result [Trap] = NONE`

(* 4.2.6  Function Instances *)
(* Moved up since store needs funcinst. *)

(* NOTE: Host Functions are not explicitly defined in the spec. We use them
 *       as a vehicle to index a collection of host functions that live
 *       outside the wasm store. The actual host function is then able to
 *       consume the wasm store and create a new one (conforming with the
 *       constraints on host functions mentioned in section 4.4.7.3 and
 *       formalized in section 7.5.2.3.
 *)
val _ = type_abbrev("hostfunc", ``:num``)

val _ = Datatype `
  funcinst =
(* <| type: functype; module: moduleinst; code: func |> *)
    | Native functype moduleinst func
(* <| type: functype; hostcode hostfunc |> *)
    | Host   functype hostfunc`

(* 4.2.7  Table Instances *)
(* Moved up since store needs tableinst. *)
val _ = type_abbrev("funcelem", ``:(funcaddr option)``)
val _ = Datatype `tableinst = <| elem: funcelem list; max: u32 |>`

(* 4.2.8  Memory Instances *)
(* Moved up since store needs meminst. *)
val _ = Datatype `meminst = <| data: byte vec; max: u32 |>`
val _ = Define `page_size = 65536n`
val _ = Define `bytes_to_pages x = x DIV page_size`

(* 4.2.9  Global Instances *)
(* Moved up since store needs globalinst. *)
val _ = Datatype `globalinst = <| value: val; mut: mut |>`

(* 4.2.3  Store *)
val _ = Datatype `store =
  <| funcs  :   funcinst list
   ; tables :  tableinst list
   ; mems   :    meminst list
   ; globals: globalinst list
   |>`

(* 4.2.4  Adresses [moved to wasmLang] *)
(* 4.2.5  Module Instances [moved to wasmLang] *)
(* 4.2.6  Functions Instances [moved to wasmLang] *)
(* 4.2.7  Table Instances [moved-up] *)
(* 4.2.8  Memory Instances [moved-up] *)
(* 4.2.9  Global Instances [moved-up] *)
(* 4.2.10  Export Instances [moved to wasmLang] *)
(* 4.2.11  External Values [moved to wasmLang] *)

(* 4.2.12.2  Labels *)
(* There is no necessity for a separate label type. *)
(* val _ = Datatype `label = T_Label num (instr list)` *)

(* 4.2.12.3  Frames *)
(* Definition of frame was moved to wasmLang. *)
val _ = Datatype `activation = Activation num frame`

(* 4.2.13  Administrative Instructions [moved to wasmLang] *)

(* 4.2.13.1  Block Contexts *)
(* Parameters of the constructors x are indicated as <x>. *)
val _ = Datatype `
  block =
(* B^0 ::= <val*> [_] <instr*> *)
    | B0 (val list) (instr list)
(* B^(k+1) ::= <val*> label_<n> { <instr*> } B^k end <instr*> *)
    | Bk (val list) num (instr list) block (instr list)`

val fill_b_def = Define `
fill_b 0n (B0 vs is)          filler = MAP Const vs ++ filler ++ is /\
fill_b k  (Bk vs n i1s b i2s) filler = MAP Const vs ++ [Label n i1s (fill_b (k - 1n) b filler)] ++ i2s`

(* 4.2.13.2  Configurations *)
val _ = Datatype `thread = Thread frame (instr list)`
val _ = Datatype `config = Config store thread`

(* The above definitions of threads and configs from the spec is
 * a bit heavy. We introduce triples as a shorthand notation, as
 * used in the spec.
 *)
val _ = type_abbrev("configuration", ``:(store # frame # (instr list))``)

(* To model host functions that mutate the store, we wrap the
 * confugiration once again into a structure that references host functions.
 * Over this structure we can model what happens when a host function is
 * invoked. The small step semantics in the wasm specification is simply
 * lifted to this case.
 *)
val _ = type_abbrev("hostfuncimpl", ``:store -> (val list) -> (store # result)``)
val _ = type_abbrev("environment", ``:((hostfuncimpl list) # configuration)``)

val mk_config_def = Define `mk_config (s, f, is) = Config s (Thread f is)`

(* 4.2.13.3  Evaluation Context *)
val _ = Datatype `
  e =
(* [_] *)
    | E0
(* <val*> <E> <instr*> *)
    | Ex (val list) e (instr list)
(* label_<n> { <instr*> } <E> end *)
    | Ey num (instr list) e`

val fill_e_def = Define `
fill_e E0           filler = filler /\
fill_e (Ex vs e is) filler = MAP Const vs ++ fill_e e filler ++ is /\
fill_e (Ey n is e)  filler = [Label n is (fill_e e filler)]`

(* 4.3  Numerics *)
(* 4.3.2  Integer Operations *)
(* NOTE: ctz = count trailing zeros, clz = count leading zeros, popcnt = count 1s *)
val _ = Define
  `app_unop_i Ctz c = 0w /\ app_unop_i Clz c = 0w /\ app_unop_i Popcnt c = 0w`

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

val _ = Define
            `app_testop_i testop c = (case testop of Eqz => w2n c = 0)`

val _ = Define
            `app_relop_i rop c1 c2 = (case rop of
                                          Eq => c1 = c2
                                        | Ne => c1 <> c2
                                        | Lt U => word_lt c1 c2
                                        | Lt S => w2i c1 < w2i c2
                                        | Gt U => word_gt c1 c2
                                        | Gt S => w2i c1 > w2i c2
                                        | Le U => word_le c1 c2
                                        | Le S => w2i c1 <= w2i c2
                                        | Ge U => word_ge c1 c2
                                        | Ge S => w2i c1 >= w2i c2)`

(* 4.3.3  Floating-Point Operations *)
(* NOTE: flags are ignored, as hinted in
 *       https://webassembly.github.io/spec/core/exec/numerics.html#floating-point-operations
 *)
val _ = Define `
app_unop_f Neg = float_negate /\
app_unop_f Abs = float_abs /\
app_unop_f Ceil c = round roundTowardPositive (float_to_real c) /\
app_unop_f Floor c = round roundTowardNegative (float_to_real c) /\
app_unop_f Trunc c = round roundTowardZero (float_to_real c) /\
app_unop_f Nearest c = round roundTiesToEven (float_to_real c) /\
app_unop_f Sqrt c = SND (float_sqrt roundTiesToEven c)`

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
(* TODO *)
val cvt_def = Define `cvt op t2 sxo v = NONE`
(*
val _ = Define `
 opt_word x sx = (case x of SOME y => SOME (case sx of U => x | S => ) | _ => NONE)`

val _ = Define `float_incomp x y = (float_compare x y = UN)`

val _ = Define `float_strange x = float_incomp x x`

val _ = Define `
  cvt_i32 sx v = (case v of
                   V_i32 c => NONE
                 | V_i64 c => SOME (wasm_wrap c)
                 | V_f32 c => (case sx of
                                      SOME U => NONE (* float_to_int roundTowardZero c *)
                                    | SOME S => NONE (* float_to_int roundTowardZero c *)
                                    | NONE => NONE)
                 | V_f64 c => (case sx of
                                      SOME U => NONE (* ui32_trunc_f64 c *)
                                    | SOME S => NONE (* si32_trunc_f64 c *)
                                    | NONE => NONE))`

val _ = Define `
  cvt_i64 sx v = (case v of
                   V_i32 c => (case sx of
                                      SOME U => SOME c:i64
                                    | SOME S => SOME (n2w (Num (w2i c))):i64
                                    | NONE => NONE)
                 | V_i64 c => NONE
                 | V_f32 c => (case sx of
                                      SOME U => NONE (* ui64_trunc_f32 c *)
                                    | SOME S => NONE (* si64_trunc_f32 c *)
                                    | NONE => NONE)
                 | V_f64 c => (case sx of
                                      SOME U => (* ui64_trunc_f64 c *)
                                    | SOME S => (* si64_trunc_f64 c *)
                                    | NONE => NONE))`

val _ = Define `
  cvt_f32 sx v = (case v of
                   V_i32 c => (case sx of
                                    SOME U => SOME (f32_convert_ui32 c)
                                  | SOME S => SOME (f32_convert_si32 c)
                                  | _ => NONE)
                 | V_i64 c => (case sx of
                                    SOME U => SOME (f32_convert_ui64 c)
                                  | SOME S => SOME (f32_convert_si64 c)
                                  | _ => NONE)
                 | V_f32 c => NONE
                 | V_f64 c => SOME (wasm_demote c))`

val _ = Define `
  cvt_f64 sx v = (case v of
                   V_i32 c => (case sx of
                                    SOME U => SOME (f64_convert_ui32 c)
                                  | SOME S => SOME (f64_convert_si32 c)
                                  | _ => NONE)
                 | V_i64 c => (case sx of
                                    SOME U => SOME (f64_convert_ui64 c)
                                  | SOME S => SOME (f64_convert_si64 c)
                                  | _ => NONE)
                 | V_f32 c => SOME (wasm_promote c)
                 | V_f64 c => NONE)`

val _ = Define `
  cvt t sx v = (case t of
                 T_i32 => (case (cvt_i32 sx v) of SOME c => SOME (V_i32 c) | NONE => NONE)
               | T_i64 => (case (cvt_i64 sx v) of SOME c => SOME (V_i64 c) | NONE => NONE)
               | T_f32 => (case (cvt_f32 sx v) of SOME c => SOME (V_f32 c) | NONE => NONE)
               | T_f64 => (case (cvt_f64 sx v) of SOME c => SOME (V_f64 c) | NONE => NONE))`
*)


(* 4.4  Instructions *)

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

(* Many steps operate only on the list of instructions
 * of the current thread. Since for these cases we do
 * not care about store and frame, we write them down
 * separately and lift them to the more general case
 * afterwards.
 *)

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-s->",
  term_name = "step_simple"
}
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "↝",
  term_name = "step_simple"
}

val (step_simple_rules, step_simple_cases, step_simple_ind) = Hol_reln `
(* 4.2.13.3 *)
(!e. e <> E0 ==> fill_e e [Trap] -s-> [Trap]) /\
(!n f. [Frame n f [Trap]] -s-> [Trap]) /\
(* 4.4.1.2 *)
(!op v c. v = V_i32 c ==>
  [Const v; Unop_i (typeof v) op] -s-> [Const (V_i32 (app_unop_i op c))]
) /\
(!op v c. v = V_i64 c ==>
  [Const v; Unop_i (typeof v) op] -s-> [Const (V_i64 (app_unop_i op c))]
) /\
(!op v c. v = V_f32 c ==>
  [Const v; Unop_f (typeof v) op] -s-> [Const (V_f32 (app_unop_f op c))]
) /\
(!op v c. v = V_f64 c ==>
  [Const v; Unop_f (typeof v) op] -s-> [Const (V_f64 (app_unop_f op c))]
) /\
(* 4.4.1.3 *)
(!op v1 v2 c1 c2. v1 = V_i32 c1 /\ v2 = V_i32 c2 ==>
    [Const v1; Const v2; Binop_i (typeof v1) op]
  -s->
    [wrap_option V_i32 (app_binop_i op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_i64 c1 /\ v2 = V_i64 c2 ==>
    [Const v1; Const v2; Binop_i (typeof v1) op]
  -s->
    [wrap_option V_i64 (app_binop_i op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_f32 c1 /\ v2 = V_f32 c2 ==>
    [Const v1; Const v2; Binop_f (typeof v1) op]
  -s->
    [wrap_option V_f32 (app_binop_f op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_f64 c1 /\ v2 = V_f64 c2 ==>
    [Const v1; Const v2; Binop_f (typeof v1) op]
  -s->
    [wrap_option V_f64 (app_binop_f op c1 c2)]
) /\
(* 4.4.1.4 *)
(!op v c. v = V_i32 c ==>
  [Const v; (Testop_i (typeof v) op)] -s-> [wrap_bool (app_testop_i op c)]
) /\
(!op v c. v = V_i64 c ==>
  [Const v; (Testop_i (typeof v) op)] -s-> [wrap_bool (app_testop_i op c)]
) /\
(* 4.4.1.5 *)
(!op v1 v2 c1 c2. v1 = V_i32 c1 /\ v2 = V_i32 c2 ==>
    [Const v1; Const v2; Relop_i (typeof v1) op]
  -s->
    [wrap_bool (app_relop_i op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_i64 c1 /\ v2 = V_i64 c2 ==>
    [Const v1; Const v2; Relop_i (typeof v1) op]
  -s->
    [wrap_bool (app_relop_i op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_f32 c1 /\ v2 = V_f32 c2 ==>
    [Const v1; Const v2; Relop_f (typeof v1) op]
  -s->
    [wrap_bool (app_relop_f op c1 c2)]
) /\
(!op v1 v2 c1 c2. v1 = V_f64 c1 /\ v2 = V_f64 c2 ==>
    [Const v1; Const v2; Relop_f (typeof v1) op]
  -s->
    [wrap_bool (app_relop_f op c1 c2)]
) /\
(* 4.4.1.6 *)
(!op v t2 sxo.
  [Const v; Cvtop t2 op (typeof v) sxo] -s-> [wrap_option (\x.x) (cvt t2 op v sxo)]
) /\
(* 4.4.2.1 *)
(!v. [Const v; Drop] -s-> []) /\
(* 4.4.2.2 *)
(!v a b. [a; b; wrap_bool v; Select] -s-> [if v then a else b]) /\
(* 4.4.3.3 *)
(!c x. [c; Tee_local x] -s-> [c; c; Set_local x]) /\
(* 4.4.5.1 *)
[Nop] -s-> [] /\
(* 4.4.5.2 *)
[Unreachable] -s-> [Trap] /\
(* 4.4.5.3 *)
(!t is. [Block t is] -s-> [Label (LENGTH t) [] is]) /\
(* 4.4.5.4 *)
(!t is. [Loop t is] -s-> [Label 0 [Loop t is] is]) /\
(* 4.4.5.5 *)
(!t i1s i2s v.
  [wrap_bool v; If t is1 is2] -s-> [Label (LENGTH t) [] (if v then i1s else i2s)]
) /\
(* 4.4.5.6 *)
(!is l vs. EVERY is_val vs ==>
  [Label (LENGTH vs) is (fill_b l holed (vs ++ [Br (n2w l)]))] -s-> vs ++ is
) /\
(* 4.4.5.7 *)
(!v l.
  [wrap_bool v; Br_if l] -s-> (if v then [Br l] else [])
) /\
(* 4.4.5.8 *)
(!i ls ln.
    [Const (V_i32 (n2w i)); Br_table ls ln]
  -s->
    [Br (if i < (LENGTH ls) then (EL i ls) else ln)]
) /\
(* 4.4.6.2 *)
(!n is vs. (EVERY is_val vs) ==> [Label n is vs] -s-> vs) /\
(* TODO: Conrad Watt also defines the following case. Not sure if needed? *)
(!n is. [Label n is [Trap]] -s-> [Trap])
`

(* Now, the steps that involve store and/or frame. *)
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "--->",
  term_name = "step"
}
val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "↪",
  term_name = "step"
}

(* s (f is) *)
val (step_rules, step_cases, step_ind) = Hol_reln `
(* lift -s-> *)
(!s f is is'. (is -s-> is') ==> (s, f, is) ---> (s, f, is')) /\
(* 4.2.13.3 *)
(!s f' f'' n. (s, f', is) ---> (s', f'', is') ==> (s, f, [Frame n f' is]) ---> (s', f, [Frame n f'' is'])) /\
(* 4.4.3.1 *)
(!s f x. (s, f, [Get_local (n2w x)]) ---> (s, f, [Const (EL x f.locals)])) /\
(* 4.4.3.2 *)
(!s f x v. (s, f, [Const v; Set_local (n2w x)]) ---> (s, (f with locals := LUPDATE v x f.locals), [])) /\
(* 4.4.3.4 *)
(!s f x. (s, f, [Get_global (n2w x)]) ---> (s, f, [Const (EL (EL x f.module.globaladdrs) s.globals).value])) /\
(* 4.4.3.5 *)
(* 4.4.4.1 *)
(!s f. (a = HD f.module.memaddrs /\ m = (EL a s.mems) /\ ea = word_add i ma.offset /\ n = bit_width t /\ (w2n ea) + (n DIV 8) <= (LENGTH m.data) /\ bs = m ) ==> (s, f, [Const (V_i32 i); Load t NONE ma]) ---> (s, f, [mk t bs])) /\
(* 4.4.4.2 *)
(* 4.4.4.3 *)
(!s f. (s, f, [Current_memory]) ---> (s, f, [Const (V_i32 (n2w (bytes_to_pages (LENGTH (EL (HD f.module.memaddrs) s.mems).data))))])) /\
(* 4.4.5.9 *)
(!s f vs n k. (n = LENGTH vs) ==> (s, f, [Frame n f (fill_b b k (vs ++ [Return]))]) ---> (s, f, vs)) /\
(* 4.4.5.10 *)
(!s f x. (s, f, [Call (n2w x)]) ---> (s, f, [Invoke (EL x f.module.funcaddrs)])) /\
(* 4.4.5.11 *)
(* 4.4.7.1 *)
(! s f a t1s t2s m mod. (has s.funcs a (Native (t1s _> t2s) mod code)) /\ ts = code.locals /\ Expr is = code.body /\ m = LENGTH t2s ==>
     (s, f, (MAP Const vs) ++ [Invoke a])
   --->
     (s, f, [Frame m <| module := mod; locals := vs ++ (MAP zero t1s) |> [Block t2s is]])
) /\
(* 4.4.7.2 *)
(! s f n vs. n = LENGTH vs ==> (s, f, [Frame n f vs]) ---> (s, f, vs))
`

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-e->",
  term_name = "step_expr"
}

val _ = Hol_reln `
(!s f is s' f' is'. (s, f, is) ---> (s', f', is') ==>
  (s, f, Expr is) -e-> (s', f', Expr is')
)`

val _ = set_mapped_fixity {
  fixity    = Infix(NONASSOC, 450),
  tok       = "-c->",
  term_name = "step_complex"
}

val (step_complex_rules, step_complex_cases, step_complex_ind) = Hol_reln `
(* lift ---> *)
(! hfs s s' f f' is is'. (s, f, is) ---> (s', f', is') ==> (hfs, (s, f, is)) -c-> (hfs, (s', f', is'))) /\
(* 4.4.7.3 *)
(* TODO: Ensure that s' extends s. *)
(! hfs s s' f hf t a r. has s.funcs a (Host t hf) /\ (EL hf hfs) s vs = (s', r) /\ arguments_ok vs t ==>
     (hfs, (s, f, (MAP Const vs) ++ [Invoke a]))
   -c->
     (hfs, (s', f, [wrap_option (\x.x) r]))
)
`

(* 7.5  Soundness *)
(* TODO *)
val _ = export_theory ()
