(** Generates UI screens that display basic blocks and parts of blocks. *)

open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [enter ()] generates a screen that displays info about the basic block
      the debugger is entering. *)
  val enter : unit -> event Machine.t

  (** [show ()] shows the current BIL instruction that the debugger is
      looking at. If [~with_nearest:"3"] is specified, then the nearest 
      +/- 3 surrounding BIL instructions will also be displayed.
      This function can take an optional [~prompt], to ask for user
      input after the BIL instructions are displayed, and a [~handler],
      to process that input. *)
  val show : ?prompt:Ui.output option -> 
    ?handler:(Ui.input -> event Machine.t) option -> 
    ?with_nearest:string option -> unit -> event Machine.t

  (** [always_show "3"] tells the debugger's cursor to always show the nearest
      +/- 3 terms (BIL instructions) surrounding the current term. It can
      also take an optional [~prompt], to ask the user for input after
      it has finished setting the number of terms to show, and a [~handler],
      to process that input. *)
  val always_show : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string ->
    event Machine.t

end
