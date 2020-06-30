(** Generates screens for setting/displaying variables/registers. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [show_var "RAX"] generates a screen that displays the value stored
      in RAX. If there is no variable named "RAX", then this function
      returns an error screen instead. This function also takes an optional 
      [~prompt], to ask the user for input after it displays the value, 
      and a [~handler], to process that input. *)
  val show_var : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string -> 
    event Machine.t

  (** [show_regs ()] generates a screen that displays all the general
      purpose registers and their values. It also takes an optional
      [~prompt], to ask the user for input after it shows all the registers,
      and a [~handler], to process that input. *)
  val show_regs : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

  (** [show_all ()] generates a screen that displayss all the variables
      and their values that exist in the environment. This can be a fairly
      large set. This function also takes an optional [~prompt], to ask the
      user for input after it has displayed all the variables, and a 
      [~handler], to process that input. *)
  val show_all : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> unit -> event Machine.t

  (** [set_var "RAX" "0xabc"] sets the value of RAX to 0xABC, and then
      generates a screen displaying that this happened. If there is no such
      variable with that name, or if the value is not in a valid hex format,
      this function returns an error screen instead. It can also take an
      optional [~prompt], to ask the user for input after it has displayed
      a successful message, and a [~handler], to process that input. *)
  val set_var : ?prompt:Ui.output option ->
    ?handler:(Ui.input -> event Machine.t) option -> string -> string ->
    event Machine.t

end
