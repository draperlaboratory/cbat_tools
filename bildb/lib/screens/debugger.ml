(** Implements {!Debugger}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  module Cursor = Cursor.Make (Machine)
  module Help = Help.Make (Machine)
  module Block = Blocks.Make (Machine)
  module Breakpoint = Breakpoints.Make (Machine)
  module Variable = Variables.Make (Machine)
  module Location = Locations.Make (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* This handler processes debugger commands. It checks if the user
     entered [h] (to display the help), or [q] to quit, or [s] (to step
     to the next instruction), or whatever, and it dispatches the 
     next screen/event accordingly. *)
  let rec main_loop (s : Ui.input) : event Machine.t =
    let prompt = Utils.prompt in
    let handler = Some main_loop in
    let input = Ui.string_of_input s in
    let%bind _ =
      if String.is_empty input then Machine.return ()
      else Cursor.set_last_cmd (Some s) in
    match Utils.words_of input with

    (* The user wants to quit. *)
    | ["q"] -> Machine.return (Event.quit ())

    (* The user wants to see the help. *)
    | ["h"] -> Help.menu () ~prompt ~handler

    (* The user wants to step to the next term (BIL instruction). *)
    | ["s"] ->
      begin
        let%bind _ = Cursor.set_step_mode () in
        Machine.return (Event.finished ())
      end

    (* The user wants to step to the previous term (BIL instruction). *)
    | ["-s"] ->
      begin
        let%bind _ = Cursor.set_step_mode () in
        let%bind _ = Cursor.set_backward () in
        let%bind _ = Cursor.backstep () in
        Machine.return (Event.finished ())
      end

    (* The user wants to skip to the next block/breakpoint. *)
    | ["n"] ->
      begin
        let%bind _ = Cursor.set_next_mode () in
        Machine.return (Event.finished ())
      end

    (* The user wants to skip to the previous block/breakpoint. *)
    | ["-n"] ->
      begin
        let%bind _ = Cursor.set_next_mode () in
        let%bind _ = Cursor.set_backward () in
        let%bind _ = Cursor.backstep () in
        Printf.printf "----- Done with one backstep\n%!";
        Machine.return (Event.finished ())
      end

    (* The user wants to see the nearest +/- [n] terms (BIL instructions) 
       around the current one. *)
    | ["show"; n] ->  
      Block.show () ~with_nearest:(Some n) ~prompt ~handler

    (* The user always wants to see the nearest +/- [n] terms
       (BIL instructions) around the current one. *)
    | ["always"; "show"; n] ->
      Block.always_show n ~prompt ~handler

    (* The user wants to set a breakpoint at [tid]. *)
    | ["b"; tid] ->
      Breakpoint.set tid ~prompt ~handler

    (* The user wants to clear a breakpoint at [tid]. *)
    | ["clear"; tid] ->
      Breakpoint.clear tid ~prompt ~handler

    (* The user wants to see all active breakpoints. *)
    | ["breaks"] ->
      Breakpoint.show () ~prompt ~handler

    (* The user wants to see all variables in the environment. *)
    | ["all"] ->
      Variable.show_all () ~prompt ~handler

    (* The user wants to see the values of all registers. *)
    | ["regs"] ->
      Variable.show_regs () ~prompt ~handler

    (* The user wants to print the value of [name]. *)
    | ["p"; name] ->
      begin

        (* If [name] a hex word, it's an address, so the user wants
           to see the value stored at that address. *)
        if Utils.is_hex name then
          let num_words = "1" in
          Location.show_locs name ~prompt ~handler ~num_words

        (* Otherwise, it must be the name of a variable/register,
           so the user wants to see the value of that. *)
        else
          Variable.show_var name ~prompt ~handler

      end

    (* The user wants to print [num_words] starting at [addr]. *)
    | ["p"; addr; num_words] ->
      Location.show_locs addr ~prompt ~handler ~num_words

    (* The user wants to set a value. *)
    | ["set"; assignment] ->
      begin

        (* If we can't extract a key/value, show an error screen. *)
        match Utils.key_val_of assignment with
        | None ->
          begin
            let text = Utils.invalid_msg in
            Machine.return (Event.screen () ~text ~prompt ~handler)
          end

        (* If we can extract a key value, we can move on. *)
        | Some (key, value) ->
          begin

            (* If the key is a hex word, it's an address, so the user
               wants to store a value at an address. *)
            if Utils.is_hex key then
              Location.set_loc key value ~prompt ~handler

            (* Otherwise, it's the name of a variable/register, and the
               user wants to store a value there. *)
            else
              Variable.set_var key value ~prompt ~handler

          end
      end

    (* If there's no input, the user hit the [enter] key *)
    | [] ->
      begin
        let%bind last_cmd = Cursor.get_last_cmd () in
        match last_cmd with
        | Some cmd -> print_endline "here"; main_loop cmd
        | None ->
          begin
            print_endline "there";
            let text = Utils.invalid_msg in
            Machine.return (Event.screen () ~text ~prompt ~handler)
          end
      end

    (* Anything else is an unrecognized command. Display an error screen. *)
    | _ ->
      begin
        let text = Utils.invalid_msg in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

end
