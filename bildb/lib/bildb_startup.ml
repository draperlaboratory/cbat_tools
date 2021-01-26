(** Implements {!Startup}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module State = Bildb_state
module Ui = Bildb_ui
module Architecture = Bildb_architecture
module Initialization = Bildb_initialization
module Data = State.Data

module type Configuration = sig
  val initial_state : Data.t option
end

module Make (Conf : Configuration) (Machine : Primus.Machine.S) = struct
  module Env = Primus.Env.Make (Machine)
  module Mem = Primus.Memory.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module UI = Ui.Make (Machine)
  module Event = Ui.Event (Machine)
  module Architecture = Architecture.Make (Machine)
  module Init = Initialization.Make (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  (* Finds a variable by name (if any) in the environment. *)
  let find_var (name : string) : Var.t option Machine.t =
    let* vars = Env.all in
    let var = Seq.find vars ~f:(fun r -> String.equal (Var.name r) name) in
    Machine.return (var)

  (* A helper to set a variable in a machine. *)
  let set_variable (v : Var.t) (w : Word.t) : unit Machine.t =
    let* value = Value.of_word w in
    Env.set v value

  (* Set the variables specified in [state] to the provided values. *)
  let initialize_variables (state : Data.t) : unit Machine.t =
    let vars = Data.variables state in
    let output = List.map vars ~f:(fun variable ->
      let w = Data.word_of_var_value variable in
      let* var = find_var (Data.string_of_var_key variable) in
      match var with
      | None -> Machine.return ()
      | Some v -> set_variable v w)
      in
    Machine.sequence output

  (* Set the locations specified in [state] to the provided values. *)
  let initialize_locations (state : Data.t) : unit Machine.t =
    let locs = Data.locations state in
    let output = List.map locs ~f:(fun location ->
      let a = Data.word_of_loc_address location in
      let w = Data.word_of_loc_value location in
      let* is_mapped = Mem.is_mapped a in
      let* _ = if is_mapped
        then Machine.return ()
        else Mem.allocate a 1
        in
      Mem.store a w)
      in
    Machine.sequence output

  (* This function is triggered when {Primus.System.init} fires.
     This function will print info about the architecture, and
     it will initialize the machine if any initial state has
     been specified. *)
  let initialize () : unit Machine.t =

    (* Get info about the machine architecture, and generate a screen
       to display that info. *)
    let* screen = Architecture.about () in
    let* _ = UI.render screen in

    (* If any initial state has been specified, initialize the machine
       accordingly, and generate a screen to display what was initialized. *)
    match Conf.initial_state with
    | Some state ->
      begin
        let* _ = initialize_variables state in
        let* _ = initialize_locations state in
        let* screen = Init.show state in
        let* _ = UI.render screen in
        Machine.return ()
      end

    (* If no initial state was specified, we're done. *)
    | None -> Machine.return ()

  (* Subscribe to the Primus initialization event. *)
  let init () =
    let open Machine.Syntax in
    Machine.sequence [
      Primus.System.init >>> initialize;
    ]

end
