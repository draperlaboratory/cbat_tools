(** For handling lines of text that can be printed to a TTY. *)

(** Different styles that a line can be formatted with. *)
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

(** This represents a line of output that can be printed to a terminal. *)
type t

(** [mk ~color:Red "hello"] generates the line "hello" styled red. *)
val mk : ?style:style -> ?color:color -> ?newline:string -> string -> t 

(** [for_terminal text] formats [text] for printing to the terminal.
    The result is a string which, if piped to the terminal, will be
    printed with the appropriate styling (red, bold, etc.) *) 
val for_terminal : t -> string

(** [to_string text] returns just the string content of [text], without
    any formatting/styling. *)
val to_string : t -> string

(** Clears the terminal screen and puts the cursor back at the top. *)
val wipe_screen : unit -> unit
