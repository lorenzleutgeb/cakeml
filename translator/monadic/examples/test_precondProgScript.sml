(*
  An example showing how to use the monadic translator with
  references, arrays and exceptions.
*)

open preamble ml_monad_translator_interfaceLib

val _ = new_theory "test_precondProg"

(* Create the data type to handle the references *)
Datatype:
  state_refs = <| the_num : num ;
                  the_num_array : num list ;
                  the_int_array : int list |>
End

(* Data type for the exceptions *)
Datatype:
  state_exn = Fail string | Subscript
End

val config =  global_state_config |>
              with_state ``:state_refs`` |>
              with_exception ``:state_exn`` |>
              with_refs [("the_num", ``0 : num``)] |>
              with_resizeable_arrays [
                ("the_num_array", ``[] : num list``,
                  ``Subscript``, ``Subscript``),
                ("the_int_array", ``[] : int list``,
                  ``Subscript``, ``Subscript``)
              ];

Overload failwith = ``raise_Fail``

val _ = start_translation config;

val hd_v_thm = translate HD;
val tl_v_thm = translate TL;
val el_v_thm = translate EL;

(* Some tests *)
val f1_def = Define `
  f1 x y (z : num) = return (x + y + z)`;
val f1_v_thm = m_translate f1_def;

val f2_def = Define `
  f2 x y (z : num) = return ((HD x) + y + z)`;
val f2_v_thm = m_translate f2_def;

val f3_def = Define `
  f3 x = return (HD x)`;
val f3_v_thm = m_translate f3_def;

val f4_def = Define `
  f4 x = do y <- return x; return y od`;
val f4_v_thm = m_translate f4_def;

val f5_def = Define `
  f5 l n1 = do
    n2 <- get_the_num;
    return (EL (n1 + n2) l)
  od`;
val f5_v_thm = m_translate f5_def;

val f6_def = Define `
  f6 l n = f5 l n`;
val f6_v_thm = m_translate f6_def;

val f7_def = Define `
  f7 x y z = f1 x y z`;
val f7_v_thm = m_translate f7_def;

val f8_def = Define `
  (f8 (x::xs) n = (do l <- f8 xs n; return (1+l) od)) /\
  (f8 [] n = return (n : num))`;
val f8_v_thm = m_translate f8_def;

val f9_def = Define `
  (f9 (x::xs) n = (do l <- f9 xs n; return (1+l) od)) /\
  (f9 [] n = return ((HD n) : num))`;
val f9_v_thm = m_translate f9_def;

val f10_def = Define `
  f10 y = handle_Fail (
    do x <- (raise_Fail "fail");
       return x
    od
  ) (\e. return e)`;
val f10_v_thm = m_translate f10_def;

val f11_def = Define `
  f11 x = case x of []    => return (0 : num)
                  | x::xs => (do l <- f11 xs; return (1 + l) od)`;
val f11_v_thm = m_translate f11_def;

val f12_def = Define`
  f12 x = ((return (1:num)) otherwise (return 0))`;
val f12_v_thm = m_translate f12_def;

(* Mutually recursive function with preconditions *)
Datatype:
  tree = T1 (num list) | T2 (tree list)
End

val _ = register_type ``:tree``;

val _ = ParseExtras.temp_tight_equality();

val tree_sum_def = Define `
  tree_sum  (T1 l) = return (HD l) /\
  tree_sum  (T2 x) = tree_suml x /\
  tree_suml []     = return 0 /\
  tree_suml (t::l) = do
      x1 <- tree_sum t;
      x2 <- tree_suml l;
      return (x1 + x2)
    od`;
val tree_sum_v_thm = m_translate tree_sum_def;

(* No precondition *)
val tree_sum2_def = Define `
  tree_sum2  (T1 l) = return (1 : num) /\
  tree_sum2  (T2 x) = tree_suml2 x /\
  tree_suml2 []     = return 0 /\
  tree_suml2 (t::l) = do
    x1 <- tree_sum2 t;
    x2 <- tree_suml2 l;
    return (x1 + x2)
  od`
val tree_sum2_v_thm = m_translate tree_sum2_def;

(* pattern matching *)
val tree_sum3_def = Define `
  tree_sum3  (T1 l) = return (HD l) /\
  tree_sum3  (T2 x) = tree_suml3 x /\
  tree_suml3 []     = return 0 /\
  tree_suml3 (t::l) = do
    x1 <- tree_sum3 t;
    x2 <- tree_suml3 l;
    return (x1 + x2)
  od`;
val tree_sum_v_thm = m_translate tree_sum_def;

val _ = export_theory ();
