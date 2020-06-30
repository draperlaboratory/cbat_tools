(** Generates UI screens displaying info about subroutines. *)

open Bap.Std
open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [enter s] generates a screen that displays informatino about
      the subroutine [s]. *)
  val enter : Sub.t -> event Machine.t

  (** [arg a] generates a screen that displays information about
      the argument [a] to a subroutine. *)
  val arg : Arg.t -> event Machine.t

end
