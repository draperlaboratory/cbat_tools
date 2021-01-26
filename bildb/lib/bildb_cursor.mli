(** An internal cursor for the debugger.

    The cursor keeps track of where the debugger is, in the program. 
    In particular, it keeps track of the following:
    - The current basic block the user is moving through.
    - The current TID that the user is looking at.
    - The breakpoints that have been assigned to TIDs.

    It also controls how the debugger moves. It has these modes:
    - It can be in "step mode" or "next mode." Step mode means to stop at
      each term (BIL instruction) and let the user debug. Next mode means
      to skip from term to term until it reaches the next basic block
      or breakpoint. 
    - It can be in "forward" or "backward" mode, which means that it moves
      forward or backward through the terms (BIL instructions). 

    There is a {!Data} module that acts as a container to hold this
    information, and a {!Make} functor, to construct a module with
    getters/setters for the cursor data. The {!Make} fuctor also provides 
    a function [run_from tid] that tells the cursor to start moving, in 
    whatever mode it is in, from the specified [tid], and a [backstep] 
    function that tells the cursor to move backwards a step. *)

open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui

(** This module is a container to hold/manage the cursor's data. *)
module Data : sig

  (** A type to represent the data. *)
  type t

  (** A container to hold {t}, that can be stashed/retrieved in/from
      the {Primus.Machine.State} framework. *)
  val data : t Primus.Machine.State.t

end

(** This functor makes a module with getters/setters to access cursor data. *)
module Make : functor (Machine : Primus.Machine.S) -> sig

  (** [get_blk ()] returns the {Blk.t}, if any, that the cursor 
      is currently moving through. *)
  val get_blk : unit -> Blk.t option Machine.t

  (** [get_blk_exn ()] is the same as [get_blk], but with no option.
      An exception is raised if there is no such block set in the
      cursor's records. *)
  val get_blk_exn : unit -> Blk.t Machine.t

  (** [set_blk b] sets [b] as the block the cursor is moving through. *)
  val set_blk : Blk.t option -> unit Machine.t

  (** [get_tid ()] returns the {Tid.t}, if any, that the cursor
      is currently pointing at. *)
  val get_tid : unit -> Tid.t option Machine.t

  (** [get_tid_exn ()] is the same as [get_tid], but without the option.
      An exception is raised if no {Tid.t} is set in the cursor's records. *)
  val get_tid_exn : unit -> Tid.t Machine.t

  (** [set_tid tid] sets [tid] as the {Tid.t} the cursor is looking at. *)
  val set_tid : Tid.t option -> unit Machine.t

  (** [mark_just_visited ()] makes a note in the cursor's internal
      records that it has just visited the current term (whatever that
      term may be). *)
  val mark_just_visited : unit -> unit Machine.t

  (** [mark_not_just_visited ()] makes a note in the cursor's internal
      records that it has not just visited the current term (whatever
      that term may be). *)
  val mark_not_just_visited : unit -> unit Machine.t

  (** [was_just_visited ()] checks the cursor's internal records to see if
      the current term (whatever that term may be) was just visited. *)
  val was_just_visited : unit -> bool Machine.t

  (** [mark_just_reached_start ()] makes a note in the cursor's internal
      records that it just reached the start of the program. *)
  val mark_just_reached_start : unit -> unit Machine.t

  (** [mark_didnt_just_reach_start ()] makes a note in the cursor's internal
      records that it didn't just reach the start of the program. *)
  val mark_didnt_just_reach_start : unit -> unit Machine.t

  (** [just_reached_start ()] checks the cursor's internal records to see if
      the cursor just reached the start of the program. *)
  val just_reached_start : unit -> bool Machine.t

  (** [set_step_mode ()] puts the cursor in step mode. *)
  val set_step_mode : unit -> unit Machine.t

  (** [set_next_mode ()] puts the cursor in next mode. *)
  val set_next_mode : unit -> unit Machine.t

  (** [is_step_mode ()] checks if the cursor is in step mode. If it is not,
      then it will be in next mode. *)
  val is_step_mode : unit -> bool Machine.t

  (** [set_forward ()] puts the cursor in forward mode. *)
  val set_forward : unit -> unit Machine.t

  (** [set_backward ()] puts the cursor in backward mode. *)
  val set_backward : unit -> unit Machine.t

  (** [is_forward ()] checks if the cursor is in forward mode. If it is not,
      then it will be in backward mode. *)
  val is_forward : unit -> bool Machine.t

  (** [get_breaks ()] gets the list of breakpoints (a list of {Tid.t}s)
      that are currently set. *)
  val get_breaks : unit -> Tid.t list Machine.t

  (** [add_break tid] adds [tid] to the list of breakpoints. *)
  val add_break : Tid.t -> unit Machine.t

  (** [remove_break tid] removes [tid] from the list of breakpoints. *)
  val remove_break : Tid.t -> unit Machine.t

  (** [is_break tid] checks if [tid] has a breakpoint associated with it. *)
  val is_break : Tid.t -> bool Machine.t

  (** [get_show_nearest ()] gets the number of +/- nearest terms
      (BIL instructions) that the cursor should show when the user
      looks at a term (BIL instruction). *) 
  val get_show_nearest : unit -> int Machine.t

  (** [set_show_nearest n] tells the cursor that whenever a user looks at
      a term (BIL instruction), it should also show the nearest [n] +/- terms
      (BIL instructions) around that term. *)
  val set_show_nearest : int -> unit Machine.t

  (** [get_last_cmd ()] returns the last command the user typed (if any). *)
  val get_last_cmd : unit -> Ui.input option Machine.t

  (** [set_last_cmd (Some "foo")] stores [Some "foo"] as the last command
      the user typed in. *)
  val set_last_cmd : Ui.input option -> unit Machine.t

  (** [is_stopping_point tid] checks if [tid] is a term where the debugger
      should stop. If the debugger's cursor is moving in next mode, it
      will stop at a breakpoint, or a basic block. So this function checks
      if [tid] is a breakpoint or basic block. *)
  val is_stopping_point : Tid.t -> bool Machine.t

  (** [is_initial_machine] checks if the current Primus machine is the
      original/initial machine that started the whole thing. *)
  val is_initial_machine : unit -> bool Machine.t

  (** [update tid] tells the cursor to update its internal records so it
      is pointing at the provided [tid]. The cursor will also update the
      basic block in its records, to the one the provided [tid] is 
      contained in. *)
  val update : Tid.t -> unit Machine.t

  (** [backstep ()] causes the cursor to move backwards one term
      (i.e., one BIL instruction). *)
  val backstep : unit -> unit Machine.t

  (** [run_from tid] lets the cursor start moving from the provided [tid],
      in whatever mode it is in. If the cursor is in forward step or next 
      mode, it will step to the next term (BIL instruction) or skip ahead
      until it reaches the next breakpoint or basic block. If the cursor
      is in backward step or next mode, it will step to the previous term
      or skip backwards until it reaches the nearest breakpoint or start
      of a basic block. *)
  val run_from : Tid.t -> unit Machine.t

end
