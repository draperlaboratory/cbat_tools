(** Generates the UI screen that displays architecture information. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [about ()] generates a screen that displays info about 
      the machine architecture (e.g., x86_64, etc). *)
  val about : unit -> event Machine.t

end
