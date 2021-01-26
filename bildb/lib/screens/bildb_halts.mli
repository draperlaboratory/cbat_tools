(** Generates UI screens that display info about halting Primus machines. *)

open Bap_primus.Std

module Ui = Bildb_ui

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [fini ()] generates a screen which says Primus is finished.
      It can take an optional [~prompt], to ask the user for input
      after it displays its message, and a [~handler], to process
      that input. *)
  val fini : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

  (** [div_by_zero ()] generates a screen which says that a division by
      zero trap was signaled. It can take an optional [~prompt], to ask
      the user for input after it displays its message, and a [~handler],
      to process that input. *)
  val div_by_zero : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

  (** [exn_raised e] generates a screen which says that an exception was
      raised in a machine, and it displays the exception. This function
      can also be given an optional [~prompt], to ask the user for
      input after it displays its message, and a [~handler], to 
      process that input. *)
  val exn_raised : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> Machine.Id.t ->
    Primus.Exn.t -> event Machine.t

  (** [halt cid] generates a screen which says that the machine with
      ID [cid] has halted. It can take an optional [~prompt], to ask the
      user for input after it has displayed its message, and a [~handler],
      to process that input. *)
  val halt : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> Machine.Id.t ->
    event Machine.t

  (** [interrupt mid n] generates a screen which says that interrupt [n]
      was signaled in the machine with ID [mid]. It can take an optional
      [~prompt], to ask the user for input after it has displayed its
      message, and a [~handler], to process that input. *)
  val interrupt : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> Machine.Id.t ->
    int -> event Machine.t

end
