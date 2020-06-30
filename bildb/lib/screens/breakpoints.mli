(** Generates UI screens that deal with setting/displaying breakpoints. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [set "%000000fa"] will set a breakpoint at TID 000000fa and then
      generate a screen displaying that this has happened. If no such
      TID exists, an error screen is returned instead. This function can
      optionally take a [~prompt], to ask for user input after the
      breakpoint is set, and a [~handler], to process that input. *) 
  val set : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string ->
    event Machine.t

  (** [clear "%000000fa"] will clear a breakpoint at TID 00000fa and then
      generate a screen displaying that this happened. If no such TID
      or breakpoint exists, it returns an error screen instead.
      This function can optionally take a [~prompt], to ask the user for
      input after the breakpoint is cleared, and a [~handler], to process
      that input. *)
  val clear : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string ->
    event Machine.t

  (** [show ()] generates a screen that displays all breakpoints that
      have been set. If none have been set, it instead generates a screen
      that says this. This function can take an optional [~prompt], to ask
      for user input after it displays the breakpoints (or lack thereof),
      and a [~handler], to process that input. *)
  val show : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

end
