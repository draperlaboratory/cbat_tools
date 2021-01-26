(** Generates UI screens for storing/reading data from memory locations. *)

open Bap_primus.Std

module Ui = Bildb_ui

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [show_locs "0x3ffffff1" ~num_words:"16"] generates a screen that
      displays the 16 consecutive bytes stored in memory, starting at
      location 0x3ffffff1. If the address or number of words strings are
      incorrectly formatted, this function will generate an error screen
      instead. If any of the addresses the user wants to read are not
      mapped/allocated, this function will also generate an error screen
      saying so. This function can take an optional [~prompt], to ask the
      user for input after it has displayed the stored bytes, and a
      [~handler] to handle that input. *)
  val show_locs : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> ?num_words:string ->
    string -> event Machine.t

  (** [set_loc "0x3fffff1" "0xab"] will store the byte 0xab at the address
      0x3ffffff1. If the address or byte strings are not formatted correctly,
      this function will generate an error screen instead. If the address
      the user wants to write to is not mapped/allocated, this function
      will generate an appropriate error screen. This function can take
      an optional [~prompt], to ask the user for input after it has
      stored the given byte, and a [~handler] to process that input. *)
  val set_loc : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string -> string ->
    event Machine.t

end
