(** Implements {!Breakpoint}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  module Cursor = Cursor.Make (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* Helper to generate an error message. *)
  let mk_msg (tid : string) : string =
      Printf.sprintf "Invalid '%s'. Must be '%s', e.g. '%s'"
      tid "%hex" "%0000007a"

  (* Checks if the provided TID actualy exists in the program. *)
  let is_real (tid : Tid.t) : bool Machine.t =
    let%bind prog = Machine.gets Project.program in
    match Program.lookup def_t prog tid with
    | Some t -> Machine.return true
    | None -> match Program.lookup jmp_t prog tid with
      | Some t -> Machine.return true
      | None -> Machine.return false

  (* Sets a breakpoint at the specified TID. The TID should be a string
     the user typed in. This function will try to parse it into a real
     {Tid.t}. If it is not in the right format (i.e., "%hex", for example
     "%000000fa"), then this function will return an error screen. If it
     is the right format, but there is no such TID in the program, this
     function will also return an error screen. Otherwise, given that the
     string parses into a real TID in the program, then this function will
     set the breakpoint and return a screen saying as much. This function
     can take an optional [~prompt], to ask the user for input after the
     breakpoint is set, and a [~handler], to process that input. *)
  let set ?prompt:(prompt=None) ?handler:(handler=None) (tid : string)
      : event Machine.t =

    (* The TID the user typed in must begin with "%". If not,
       return an error screen. *)
    if String.prefix tid 1 <> "%" then
      let text = [Ui.mk_output ~color:Tty.Red (mk_msg tid)] in
      Machine.return (Event.screen () ~text ~prompt ~handler)

    (* Try to parse the provided TID string into a {Tid.t}. *)
    else
      match Tid.from_string tid with

      (* If we got no {Tid.t}, return an error screen. *)
      | Error _ ->
        begin
          let text = [Ui.mk_output ~color:Tty.Red (mk_msg tid)] in
          Machine.return (Event.screen () ~text ~prompt ~handler)
        end

      (* If we got a {Tid.t}, we can move on. *)
      | Ok tid' ->
        begin

          (* If the {Tid.t} is a real TID in the program, set a breakpoint
             on it, and return a screen saying that this happened. *)
          let%bind is_real = is_real tid' in
          match is_real with
          | true ->
            begin
              let%bind () = Cursor.add_break tid' in
              let msg = Printf.sprintf "Breakpoint set at %s" tid in
              let text = [Ui.mk_output ~color:Tty.Green msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)
            end

          (* If there is no such TID in the program, return an
             error screen. *)
          | false ->
            begin
              let msg = Printf.sprintf "No instruction at: '%s'" tid in
              let text = [Ui.mk_output ~color:Tty.Red msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)
            end
    
        end

  (* Removes a breakpoint at the specified TID. As with the [set] function 
     above, the TID is a string typed in by a user, so this function will
     check that it is correct and return an error screen if it is not.
     If the string can be parsed into a real TID in the program, then
     this function will clear the breakpoint associated with that TID,
     and return a screen that says this happened. This function can take
     an optional [~prompt], to ask the user for input after the breakpoint
     is cleared, and a [~handler], to process that input. *)
  let clear ?prompt:(prompt=None) ?handler:(handler=None) (tid : string)
      : event Machine.t =

    (* The TID the user typed in must begin with "%". If it doesn't,
       return an error screen instead. *)
    if String.prefix tid 1 <> "%" then
      let text = [Ui.mk_output ~color:Tty.Red (mk_msg tid)] in
      Machine.return (Event.screen () ~text ~prompt ~handler)
    else

      (* Try to parse the TID string into a {Tid.t}. If that doesn't
         work, return an error srceen. *)
      match Tid.from_string tid with
      | Error _ ->
        begin
          let text = [Ui.mk_output ~color:Tty.Red (mk_msg tid)] in
          Machine.return (Event.screen () ~text ~prompt ~handler)
        end

      (* If we did get a {Tid.t}, we can proceed. *)
      | Ok tid' ->
        begin

          (* If this {Tid.t} has a breakpoint set on it, then clear it,
             and return a screen that says this was done. *)
          let%bind is_break = Cursor.is_break tid' in
          match is_break with
          | true ->
            begin
              let%bind () = Cursor.remove_break tid' in
              let msg = Printf.sprintf "Breakpoint cleared at %s" tid in
              let text = [Ui.mk_output ~color:Tty.Green msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)
            end

          (* If there is no breakpoint set on the given {Tid.t}, then
             return an error screen that says this. *)
          | false ->
            begin
              let msg = Printf.sprintf "No breakpoint at: '%s'" tid in
              let text = [Ui.mk_output ~color:Tty.Red msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)
            end

        end

  (* Generate a screen that shows all breakpoints. *)
  let show ?prompt:(prompt=None) ?handler:(handler=None) ()
      : event Machine.t =

    (* Get all the breakpoints that have been set. *)
    let%bind breaks = Cursor.get_breaks () in

    (* If there are some breakpoints, return a screen that prints them. *)
    match (List.length breaks) > 0 with
    | true ->
      begin
      let text = List.map breaks ~f:(fun b ->
        Ui.mk_output ~color:Tty.Green (Tid.to_string b)) in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* If no breakpoints are set, return a screen that says so. *)
    | false ->
      begin
        let text =
          [Ui.mk_output ~color:Tty.Red "No breakpoints have been set"] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

end
