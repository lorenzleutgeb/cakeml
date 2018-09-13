(*
   See https://tools.ietf.org/html/rfc4648
*)

open miscTheory
open HolKernel bossLib boolLib boolSimps lcsymtacs Parse libTheory
val _ = new_theory "base64"

val upper_def = Define `upper = GENLIST (CHR o ($+ 65n)) 26n`
val lower_def = Define `lower = GENLIST (CHR o ($+ 97n)) 26n`
val digit_def = Define `digit = GENLIST (CHR o ($+ 48n)) 10n`

val _ = Datatype `
  alphabet_name =
    | Base64    (* RFC4648, Section 4 *)
    | Base64URL (* RFC4648, Section 5 *)
    | Base32    (* RFC4648, Section 6 *)
    | Base32HEX (* RFC4648, Section 7 *)
    | Base16    (* RFC4648, Section 8 *)
`

val _ = Datatype `alphabet = <| name: alphabet_name; code: string; pad: char |>`

val alph_64_def = Define `
  alph_64 =
    <| name := Base64
     ; code := upper ++ lower ++ digit ++ "+/"
     ; pad  := #"="
     |>`

val alph_64_url_def = Define `
  alph_64_url =
    <| name := Base64URL
     ; code := upper ++ lower ++ digit ++ "-_"
     ; pad  := #"="
     |>`

val alph_32_def = Define `
  alph_32 =
    <| name := Base32
     ; code := upper ++ (TAKE 6 (DROP 2 digit))
     ; pad  := #"="
     |>`

val alph_32_hex_def = Define `
  alph_32_hex =
    <| name := Base32HEX
     ; code := digit ++ (TAKE 22 upper)
     ; pad  := #"="
     |>`

val alph_16_def = Define `
  alph_16 =
    <| name := Base16
     ; code := digit ++ (TAKE 6 upper)
     ; pad  := #"="
     |>`

val default_alph_def = Define `default_alph = alph_64_url`

val LIST_MUL = Define `LIST_MUL l n = FUNPOW (APPEND l) n []`

val pad_def = Define `
  pad data k c =
    if k = 0
    then ([], 0n)
    else
      let n = (LENGTH data) MOD (k + 1) in
        if n = 0
        then ([], 0n)
        else (LIST_MUL [c] (k + 1 - n), (k + 1 - n))`

val group_def = Define `
  group data m k pad = REVERSE (n2l m ((l2n 256 (REVERSE (MAP w2n data))) * (2n EXP (pad * k))))`

(* TODO: Base32 is not working... *)
val encode_alph_def = Define `
  (encode_alph alph [] = []) /\
  (encode_alph alph (data:((8 word) list)) =
    let k = 8 MOD (LOG2 (LENGTH alph.code)) in
    let (cs, bs) = pad data k alph.pad in
    let indices = group data (LENGTH alph.code) k bs in
      (MAP (\x. EL x alph.code) indices) ++ cs
  )`

val encode_def = Define `encode = encode_alph alph_64`

(* Encoding conformant to RFC2045:
 *   Multipurpose Internet Mail Extensions (MIME) Part One:
 *   Format of Internet Message Bodies
 * see https://tools.ietf.org/html/rfc2045#section-6.8 *)
(* TODO *)
val encode_mime_def = Define `
  encode_mime = encode`

val str2bytes = Define `str2bytes = MAP (\c. n2w (ORD c): (8 word))`
val prefices = Define `prefices s = GENLIST (\i. TAKE i s) (1 + LENGTH s)`

(* val view_def = Define `view width ns = MAP (\x. word_to_bin_string (n2w_itself (x, width))) ns` *)

(* MAP (\alph. MAP ((encode_alph alph) o str2bytes) (prefices "foobar")) [alph_64; alph_64_url; alph_32; alph_32_url; alph_16] *)

(* MAP (\x. encode alph_ (MAP (n2w o ORD) x)) [""; "f"; "fo"; "foo"; "foob"; "fooba"; "foobar"] *)

val _ = export_theory()
