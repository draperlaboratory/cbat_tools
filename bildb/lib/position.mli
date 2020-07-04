(** A Primus component that triggers the debugger.

    This component subscribes to various Primus events, like when Primus
    enters a subroutine, a jump, a halt, and so on. At those points, the
    component renders screens (see {!Ui} for more on screens) that display
    information about what is happening, and it triggers the debug loop
    to ask the user what they want to do. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig

  (** Subscribes to the revelant Primus events. *)
  val init : unit -> unit Machine.t

end
