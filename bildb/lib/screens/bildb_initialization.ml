(** Implements {!Initialization}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui
module State = Bildb_state
module Tty = Bildb_tty
module Utils = Bildb_utils

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* Generate a screen to display the initial state of BILDB. *)
  let show (state : State.Data.t) : event Machine.t =

    (* A header to let the user know what we're displaying here. *)
    let header = [Ui.mk_output ~style:Tty.Bold "Initialized state"] in

    (* Make a pretty/tabulated list of initialized variables. *) 
    let variables = State.Data.variables state in
    let vars = List.map variables ~f:(fun v ->
      let name = State.Data.string_of_var_key v in
      let value = State.Data.string_of_var_value v in
      Printf.sprintf "%s: %s" (Utils.pad name Ui.key_width) value) in
    let tabulated_vars = Utils.tabulate vars Ui.screen_width in
    let vars' = List.map tabulated_vars ~f:(fun s -> Ui.mk_output s) in
    let var_output = List.cons (Ui.mk_output "Variables:") vars' in

    (* Make a pretty/tabulated list of initialized memory locations. *)
    let locations = State.Data.locations state in
    let locs = List.map locations ~f:(fun l ->
      let addr = State.Data.string_of_loc_address l in
      let value = State.Data.string_of_loc_value l in
      Printf.sprintf "%s: %s" (Utils.pad addr Ui.key_width) value) in
    let tabulated_locs = Utils.tabulate locs Ui.screen_width in
    let locs' = List.map tabulated_locs ~f:(fun s -> Ui.mk_output s) in
    let loc_output = List.cons (Ui.mk_output "Locations:") locs' in

    (* Combine all the output and put it into a screen. *)
    let first_bit = List.append header var_output in
    let next_bit = List.append first_bit loc_output in
    let text = List.append next_bit [Ui.mk_output ""] in
    Machine.return (Event.screen () ~text)

end
