(** Some basic utilities used by various other modules. *)

open Bap.Std

(** [pad "foo" 6] adds spaces after "foo" until the string is 6 chahracters
    long. [pad "foo" 2] leaves the string at 3 characters long. *)
val pad : string -> int -> string

(** [tabulate my_list 78] puts the strings in [my_list] into as many columns
    as it can fit in a 78-character wide screen. *)
val tabulate : string list -> int -> string list

(** [words_of "foo bar biz baz"] returns ["foo"; "bar"; "biz"; "baz"]. 
    It splits on all white space characters and trims each word. *)
val words_of : string -> string list

(** [key_val_of "foo=bar"] returns [Some ("foo", "bar")]. The key/val are
    stripped of whitespace. [key_val_of "foo"] returns [None]. *)
val key_val_of : string -> (string * string) option

(** [is_assignment "foo=bar"] returns [true], whereas [is_assignment "foo"]
    returns [false]. It returns [true] if an equal sign is present. *)
val is_assignment : string -> bool

(** [is_hex "0xabc"] returns [true], whereas [is_hex "abc"] returns [false].
    It returns [true] if the string begins with "0x". *)
val is_hex : string -> bool

(** [int_of_size `r32] returns [32], whereas [`r64] returns [64]. *)
val int_of_size : addr_size -> int 

(** [word_of "0x03" ~bits:8] attempts to converts 0x03 into the equivalent
    8-bit word (i.e., b00000011). It returns [None] if it can't, or [Some w]
    if it succeeds, where [w] is the word. *)  
val word_of : ?bits:int -> string -> Word.t option

(** [string_of w] converts the word [w] to a hex string. *)
val string_of : Word.t -> string

(** A default prompt to display to users when asking for input.
    This is used as the prompt for the main debug loop. *)
val prompt : Ui.output option

(** Some text to display for a generic error screen. *) 
val invalid_msg : Ui.output list
