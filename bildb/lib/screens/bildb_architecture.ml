(** Implements {!Architecture}. *)

open Core
open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui
module Utils = Bildb_utils
module Tty = Bildb_tty

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  type event = Event.t

  (* Generates a screen that displays info about the machine architecture. *)
  let about () : event Machine.t =

    (* Get architecture info. *)
    let* arch = Machine.arch in
    let arch_str = Arch.to_string arch in
    let addr_size = Utils.int_of_size (Arch.addr_size arch) in

    (* A header to let the user know what we're displaying. *)
    let header = [
      Ui.mk_output ~style:Tty.Bold "BIL Debugger";
      Ui.mk_output "Starting up...\n";
      Ui.mk_output ~style:Tty.Bold "Architecture";
      Ui.mk_output (Printf.sprintf "Type: %s" arch_str);
      Ui.mk_output (Printf.sprintf "Address size: %d" addr_size);
      Ui.mk_output "Registers:";
      ] in

    (* Make a pretty/tabulated list of general purpose registers. *)
    let module T = (val target_of_arch arch) in
    let regs = Var.Set.to_list T.CPU.gpr in
    let reg_names = List.map regs ~f:Var.to_string in
    let tabulated = Utils.tabulate reg_names Ui.screen_width in 
    let regs' = List.map tabulated ~f:(fun line -> Ui.mk_output line) in

    (* Combine all the output and put it into a screen. *)
    let text = List.append (List.append header regs') [Ui.mk_output ""] in
    Machine.return (Event.screen () ~text)

end
