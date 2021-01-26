(** Implements {!Tty}. *)

open Core_kernel

type style =
  | Plain
  | Bold
  | Dim
  | Italic
  | Underline

type color =
  | Default
  | Red
  | Green
  | Yellow
  | Blue

let start_of_style style =
  match style with
  | Plain -> "\x1b[0m"
  | Bold -> "\x1b[1m"
  | Dim -> "\x1b[2m"
  | Italic -> "\x1b[3m"
  | Underline -> "\x1b[4m"

let start_of_color color =
  match color with
  | Default -> "\x1b[39m"
  | Red -> "\x1b[31m"
  | Green -> "\x1b[32m"
  | Yellow -> "\x1b[33m"
  | Blue -> "\x1b[34m"

let end_tag = "\x1b[0m"

type t = { style : style; color : color; newline : string; text : string }

let mk 
      ?style:(style=Plain) 
      ?color:(color=Default) 
      ?newline:(newline="") 
      (text : string) 
    : t = { style; color; newline; text }

let for_terminal t : string =
  let start_style = start_of_style t.style in
  let start_color = start_of_color t.color in
  let fini =
    match (start_style, start_color) with
    | ("","") -> ""
    | _ -> end_tag
    in
  Printf.sprintf "%s%s%s%s%s" start_style start_color t.text fini t.newline

let to_string t : string = t.text

let wipe_screen () = Printf.printf "\x1b[2J\x1b[H"
