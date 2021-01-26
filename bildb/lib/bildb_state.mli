(** Handles the initial state of the machine.

    The {!Data} module is provided here to help define the initial state
    of a machine (i.e., it lets you stipulate the variables and locations
    you want initialized, and the values you want them set to). *)

open Bap.Std
open Bap_primus.Std

module Data : sig

  (* A type to represent a variable's name. *)
  type key_t

  (* A type to represent a variable's value. *)
  type value_t

  (* A type to represent a location's address. *)
  type address_t

  (* A type to represent the value that should be stored at a location. *)
  type stored_t

  (* A type to represent a variable. *)
  type variable

  (* A type to represent a location. *)
  type location

  (* A type to represent the initial state of a machine, i.e., the
     collection of variables and locations that should be initialized,
     and the values they should be initially set to. *)
  type t

  (* An empty instance of {!t}. *)
  val empty : t

  (* [var_key v] gets the name/key of [v]. *)
  val var_key : variable -> key_t

  (* [var_value v] gets the value that should be stored in [v]. *)
  val var_value : variable -> value_t

  (* [loc_address l] gets the address of [l]. *)
  val loc_address : location -> address_t

  (* [loc_value l] gets the value that should be stored in [l]. *)
  val loc_value : location -> stored_t

  (* [variables t] gets the variables that have been specified in {!t}. *)
  val variables : t -> variable list

  (* [locations t] gets the locations that have been specified in {!t}. *)
  val locations : t -> location list

  (* [mk_variable n w] creates a record which says that the variable named
     [n] should be initialized with the value [w]. *) 
  val mk_variable : string -> Word.t -> variable

  (* [mk_location a w] creates a record which says that the location at
     address [a] should be initialized with the value [w]. *)
  val mk_location : Word.t -> Word.t -> location

  (* [mk_state vars locs] creates an instance of {!t} which contains the
     variable and location records specifying what you want initialized. *)
  val mk_state : variable list -> location list -> t

  (* [with_variables t new_vars] updates {!t} with [new_vars]. *)
  val with_variables : t -> variable list -> t

  (* [with_loctaions t new_locs] updates {!t} with [new_locs]. *)
  val with_locations : t -> location list -> t

  (* [is_empty t] checks if {!t} has any variables or locations specified
     in it. *)
  val is_empty : t -> bool

  (* [find_var t n] finds the variable record in {!t} with the name [n],
     if any. *)
  val find_var : t -> key_t -> variable option

  (* [find_loc t a] finds the location record in {!t} with the address [a],
     if any. *)
  val find_loc : t -> address_t -> location option

  (* [word_of_var_value v] returns the value specified in the variable
     record, as a machine word. *)
  val word_of_var_value : variable -> Word.t

  (* [word_of_loc_address l] returns the address specified in the location
     record, as a machine word. *)
  val word_of_loc_address : location -> Word.t

  (* [word_of_loc_value v] returns the value specified in the location
     record, as a machine word. *)
  val word_of_loc_value : location -> Word.t

  (* [string_of_var v] returns the name/key of the variable record, 
     as a string suitable for printing. *)
  val string_of_var_key : variable -> string

  (* [string_of_var_value v] returns the value specified in the variable
     record as a string, suitable for printing. *)
  val string_of_var_value : variable -> string

  (* [string_of_loc_address] returns the address of the location record,
     as a string suitable for printing. *)
  val string_of_loc_address : location -> string

  (* [string_of_loc_value] returns the value specified in the address record,
     as a string suitable for printing. *)
  val string_of_loc_value : location -> string

  (* A container to hold instances of {!t}, for stashing/retrieving in
     the {Primus.Machine.State} framework. *)
  val data : t Primus.Machine.State.t

end
