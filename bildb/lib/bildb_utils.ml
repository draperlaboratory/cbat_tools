(** Implements {!Utils}. *)

open Core_kernel
open Bap.Std

module Ui = Bildb_ui
module Tty = Bildb_tty

(* Pads a string with spaces to reach the specifed [width]. *)
let pad (s : string) (width : int) : string =
  let len = String.length s in
  let diff = width - len in
  match Int.(<) width len with
  | true -> s
  | false -> String.(s ^ (make diff ' '))

(* Puts the strings from [data] into as many columns as it can to
   fill up a screen of the specified [width]. *)
let tabulate (data : string list) (width : int) : string list =
  let widest = List.fold data ~init:0 ~f:(fun acc s ->
    let len = String.length s in
    if Int.(>) len acc then len
    else acc
    ) in
  let item_width = widest + Ui.col_padding in
  let cols = width / item_width in
  let chunks = List.chunks_of data cols in
  List.map chunks ~f:(fun chunk ->
    String.concat (List.map chunk ~f:(fun s -> pad s item_width)))

(* Splits a string on white space characters and trims each word. *)
let words_of (s : string) : string list =
  let pieces = String.split_on_chars s ~on:[' '; '\t'; '\n'; '\r'] in
  List.filter pieces ~f:(fun s -> not (String.is_empty s))

(* Splits a string with an equals sign in it into [(key, value)]. *)
let key_val_of (s : string) : (string * string) option =
  let raw_pieces = String.split_on_chars s ~on:['='] in
  let pieces = List.map raw_pieces ~f:String.strip in
  match pieces with
  | [key; value] -> Some (key, value)
  | _ -> None

(* Checks if a string has an equal sign in it. If so, it's an assignment
   expression, i.e., something like ["foo=bar"]. *)
let is_assignment (s : string) : bool =
  let raw_pieces = String.split_on_chars s ~on:['='] in
  let pieces = List.map raw_pieces ~f:String.strip in
  (List.length pieces) > 0

(* Checks if a string starts with "0x". If so, we assume it's meant
   to be a hex value. *)
let is_hex (s : string) : bool = String.is_prefix s ~prefix:"0x"

(* Convert a {Bap.Std.addr_size} value into an integer (32 or 64). *)
let int_of_size (s : addr_size) : int =
  match s with
  | `r32 -> 32
  | `r64 -> 64

(* Convert a string (should be in hex format, like ["0xabc"]) into a
   binary word, if any. *)
let word_of ?bits:(bits=64) (s : string) : Word.t option =
  if not (String.is_prefix s ~prefix:"0x") then None
  else
    try
      let subject = Printf.sprintf "%s:%du" s bits in
      Some (Word.of_string subject)
    with _ -> None

(* Makes a hex string representation of a word. *)
let string_of (w : Word.t) : string = Format.asprintf "%a" Word.pp_hex w

(* The prompt to use for the main debug loop. *)
let prompt = Some (Ui.mk_output "(h for help)")

(* Some text to display in generic error screens. *)
let invalid_msg =
  [Ui.mk_output ~color:Tty.Red "Invalid input. Type h for help"]
