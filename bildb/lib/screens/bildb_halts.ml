(** Implements {!Halts}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui
module Tty = Bildb_tty

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* A default color and an error color. *)
  let color = Tty.Yellow
  let error = Tty.Red

  (* Generates a screen which says that Primus is finished. *)
  let fini ?prompt:(prompt=None) ?handler:(handler=None) ()
      : event Machine.t =
    let text = [Ui.mk_output ~style:Tty.Bold "Primus finished"] in
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Generates a screen which says a div-by-zero trap was signaled. *)
  let div_by_zero ?prompt:(prompt=None) ?handler:(handler=None) ()
      : event Machine.t =
    let msg = "Division by zero trap signaled" in
    let text = [Ui.mk_output ~color:error msg] in
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Generates a screen saying an exception was raised in a machine. *)
  let exn_raised ?prompt:(prompt=None) ?handler:(handler=None)
      (cid : Machine.Id.t) (e : Primus.Exn.t) : event Machine.t =
    match e with
    | Primus.Interpreter.Halt -> Machine.return (Event.finished ())
    | _ ->
      begin
        let mid = Machine.Id.to_string cid in
        let e' = Primus.Exn.to_string e in
        let msg = 
          Printf.sprintf "Exception raised in machine [%s]: %s" mid e' in
        let text = [Ui.mk_output ~color:error msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

  (* Generates a screen saying a machine halted. *)
  let halt ?prompt:(prompt=None) ?handler:(handler=None) 
      (cid : Machine.Id.t) : event Machine.t =
    let mid = Machine.Id.to_string cid in
    let msg = Printf.sprintf "Halting machine [%s]" mid in
    let text = [
      Ui.mk_output "----------------------------"; 
      Ui.mk_output ~color msg] in
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Generates a screen saying an interrupt was signaled in a machine. *)
  let interrupt ?prompt:(prompt=None) ?handler:(handler=None)
        (cid : Machine.Id.t) (n : int) : event Machine.t =
    let mid = Machine.Id.to_string cid in
    let msg = Printf.sprintf "Interrupt [%d] in machine [%s]" n mid in
    let text = [Ui.mk_output ~color msg] in
    Machine.return (Event.screen () ~text ~prompt ~handler)

end
