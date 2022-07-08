(** Implement {!Subroutines}. *)

open Core
open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui
module Tty = Bildb_tty

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* Generate a screen showing the TID and name of the subroutine [s]. *)
  let enter (s : Sub.t) : event Machine.t =
    let tid = Term.tid s in
    let tid_str = Tid.to_string tid in
    let name = Sub.name s in
    let msg = Printf.sprintf "Entering subroutine: [%s] %s%!" tid_str name in
    let text = [Ui.mk_output ~style:Tty.Bold msg] in
    Machine.return (Event.screen () ~text)

  (* Generate a screen displaying the argument [a]. *)
  let arg (a : Arg.t) : event Machine.t =
    let msg = String.strip (Arg.to_string a) in
    let text = [Ui.mk_output ~color:Tty.Yellow msg] in
    Machine.return (Event.screen () ~text)

end
