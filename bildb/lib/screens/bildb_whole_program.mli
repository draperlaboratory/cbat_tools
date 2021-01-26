(** Generates UI screens that display info relevant to the whole program. *)

open Bap_primus.Std

module Ui = Bildb_ui

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [start ()] generates a screen that says the user is back at the
      start of the program, if the debugger's cursor has just gone all the
      way back to the start of the program. Otherwise, this function
      returns an empty "finished" event. It can also take an optional
      [~prompt], to ask the user for input after it displays its  message,
      and a [~handler], to handle that input. *)
  val start : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

end
