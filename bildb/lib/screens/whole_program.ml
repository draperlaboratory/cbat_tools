(** Implements {!Whole_program}. *)

open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  module Cursor = Cursor.Make (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  type event = Event.t

  (* If the debugger's cursor just reached the start of the whole program,
     then this function generates a screen saying so. If the debugger 
     didn't just reach the beginning of the program, then this function
     returns an empty "finished" UI event. *) 
  let start ?prompt:(prompt=None) ?handler:(handler=None) ()
      : event Machine.t =
    let* just_reached_start = Cursor.just_reached_start () in
    match just_reached_start with
      | true ->
        begin
          let* _ = Cursor.mark_didnt_just_reach_start () in
          let text = [Ui.mk_output ~color:Tty.Red "At program start"] in
          Machine.return (Event.screen () ~text ~prompt ~handler)
        end
      | false -> Machine.return (Event.finished ())

end
