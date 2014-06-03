(*Generated by Lem from printer.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory lem_list_extraTheory astTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();



val _ = new_theory "printer"

(* observable values *)
(*open import Pervasives*)
(*open import Lib*)
(*import List_extra*)

(*open import Ast*)
(*open import SemanticPrimitives*)

val _ = Hol_datatype `
 ov =
    OLit of lit
  | OConv
  | OFn
  | OLoc
  | OError`;
 (* internal machine value (pointer) that should not appear *)

 val _ = Define `

(v_to_ov (Litv l) = (OLit l))
/\
(v_to_ov (Conv _ _) = OConv)
/\
(v_to_ov (Closure _ _ _) = OFn)
/\
(v_to_ov (Recclosure _ _ _) = OFn)
/\
(v_to_ov (Loc _) = OLoc)`;


 val _ = Define `

(ov_to_string (OLit (IntLit (i:int))) = (int_to_string i))
/\
(ov_to_string (OLit (Word8 w)) = (STRCAT"0wx"(word_to_hex_string w)))
/\
(ov_to_string (OLit (StrLit s)) = (string_to_string s))
/\
(ov_to_string (OLit (Bool T)) = "true")
/\
(ov_to_string (OLit (Bool F)) = "false")
/\
(ov_to_string (OLit Unit) = "()")
/\
(ov_to_string OConv = "<constructor>")
/\
(ov_to_string OLoc = "<ref>")
/\
(ov_to_string OFn = "<fn>")
/\
(ov_to_string OError = "<error>")`;

val _ = export_theory()

