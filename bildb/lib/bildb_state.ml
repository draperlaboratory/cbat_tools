(** Implements {!State}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Utils = Bildb_utils

(* This module encapsulates the state (variables and memory)
   that you want to initially set when the program runs. *) 
module Data = struct

  (* Type aliases for clarity/convenienc. *)
  type key_t = string
  type value_t = Word.t
  type address_t = Word.t
  type stored_t = Word.t

  (* Variables include a name/key and a value.
     Locations include an address and a value. *)
  type variable = { key : key_t; value : value_t; }
  type location = { address : address_t; value : stored_t; }

  (* The state you want initialized really boils down to a list of 
     variables and locations you want initialized when the program starts. *)
  type t = { 
    variables : variable list;
    locations : location list;
  }

  (* An empty initial state (so no variables and locations should be
     initialized, just let the program be as it is). *)
  let empty = {
    variables = [];
    locations = [];
  }

  (* Accessors for the name/key and value of variable records. *)
  let var_key (v : variable) = v.key
  let var_value (v : variable) = v.value

  (* Accessors for the address and value of location records. *)
  let loc_address (l : location) = l.address
  let loc_value (l : location) = l.value

  (* Accessors to get the variables and locations to be initialized. *)
  let variables t = t.variables
  let locations t = t.locations

  (* Constructs variable records and location records. *)
  let mk_variable (key : string) (value : Word.t) = { key; value; }
  let mk_location (address : Word.t) (value : Word.t) = { address; value; }

  (* Constructs a record of the initial state (i.e., the variables and
     locations that you want initialized when the program starts). *)
  let mk_state variables locations = { variables; locations; }

  (* Updates [t] with a new [variable] or [location] list. *)
  let with_variables t variables = { t with variables }
  let with_locations t locations = { t with locations }

  (* Checks if there are any [variable]s or [locations] specified
     that should be initialized. *)
  let is_empty t = List.is_empty t.variables && List.is_empty t.locations

  (* Finds a variable by name, or a location by address, in [t]. *)
  let find_var t k =
    List.find t.variables ~f:(fun v -> String.equal (var_key v) k)
  let find_loc t a =
    List.find t.locations ~f:(fun l -> Word.equal (loc_address l) a) 

  (* Getting words. *)
  let word_of_var_value (v : variable) : Word.t = v.value
  let word_of_loc_address (l : location) : Word.t = l.address
  let word_of_loc_value (l : location) : Word.t = l.value

  (* Stringify functions. *)
  let string_of_var_key (v : variable) : string = v.key
  let string_of_var_value (v : variable) = Utils.string_of v.value
  let string_of_loc_address (l : location) = Utils.string_of l.address
  let string_of_loc_value (l : location) = Utils.string_of l.value

  (* A container for storing initial state in the Machine's global state. *)
  let data : t Primus.Machine.State.t =
    Primus.Machine.State.declare
      ~uuid:"dabd80db-7913-4040-82e2-76182b56aefe"
      ~name:"data"
      (fun _ -> empty)

end
