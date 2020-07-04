(** Generates the UI screen that displays the initialization of BILDB. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [show state] generates a screen that displays the initialization
      data contained in [state] (see {!State.Data}). *) 
  val show : State.Data.t -> event Machine.t 

end
