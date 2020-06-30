(** Generates the UI screen that displays the help menu. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [menu ()] generates a screen that displays the help menu.
      It can optionally take a [~prompt], to ask for user input after the
      help menu is displayed, and a [~handler], to process that input. *)
  val menu : ?prompt:Ui.output option -> 
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

end
