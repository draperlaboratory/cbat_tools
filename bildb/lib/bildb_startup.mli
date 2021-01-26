(** A Primus component that runs at the startup time of Primus. 

    It does two things: (1) it gets the machine architecture and prints
    some information about it for the user, and (2) if any initial state
    is specified, it initializes all the variables and locations to the
    values specified in that state, and it prints information about what
    it's initialized for the user. *)

open Bap_primus.Std

module State = Bildb_state

(** This module is for configuring the {!Make} module. The {!Make} module
    must be parameterized with an instance of a {!Configuration} module,
    which specifies whether there is any initial state that the machine
    should be initialized with (see {!Data.State.t}). *) 
module type Configuration = sig
  val initial_state : State.Data.t option
end

(** This is the Primus component mentioned above that runs at startup.
    Note that it must be parameterized by a {!Configuration} module. *)
module Make 
    : functor (Conf : Configuration) (Machine : Primus.Machine.S) -> sig

  (* This function subscribes to the appropriate Primus events, so it
     can do its thing when Primus starts up. *)
  val init : unit -> unit Machine.t

end
