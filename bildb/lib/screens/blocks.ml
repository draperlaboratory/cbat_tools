(** Implements {!Blocks}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  module Cursor = Cursor.Make (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  type event = Event.t

  type term =
    | Blk_t of blk Term.t
    | Def_t of def Term.t
    | Jmp_t of jmp Term.t

  type t = { tid : Tid.t; term : term; }

  let color = Tty.Yellow

  let string_of t : string =
    match t.term with
    | Blk_t b -> Tid.to_string (Term.tid b)
    | Def_t d -> String.strip (Def.to_string d)
    | Jmp_t j -> String.strip (Jmp.to_string j)

  (* Get all the terms (i.e., all the BIL instructions) in a block. *)
  let terms_of (b : Blk.t) : t list =
    let blk = { tid = Term.tid b; term = Blk_t b } in
    let defs = Term.enum def_t b in
    let defs' = List.map (Seq.to_list defs)
      ~f:(fun d -> { tid = Term.tid d; term = Def_t d })
      in
    let jmps = Term.enum jmp_t b in
    let jmps' = List.map (Seq.to_list jmps)
      ~f:(fun j -> { tid = Term.tid j; term = Jmp_t j })
      in
    List.append [blk] (List.append defs' jmps')

  (* [term_in tid b ~with_nearest=3] will return the term (BIL instruction)
     with the specified [tid] that is contained in the block [b], plus the 
     nearest +/- 3 surrounding terms (BIL instructions). *)
  let term_in ?with_nearest:(nearest=0) (tid: Tid.t) (b : Blk.t) : t list =
    let terms = terms_of b in
    let len = List.length terms in
    let result = List.findi terms ~f:(fun i t -> Tid.(t.tid = tid)) in
    let i = fst (Option.value_exn result) in
    let first = if (i - nearest) < 0 then 0 else i - nearest in
    let last = if (i + 1 + nearest) > len then len else i + 1 + nearest in
    List.slice terms first last

  (* Generates a screen that displays the TID of the block the debugger
     is about to enter. *)
  let enter () : event Machine.t =
    let* tid = Cursor.get_tid_exn () in
    let msg = Printf.sprintf "Entering block %s" (Tid.to_string tid) in
    let text = [Ui.mk_output ~style:Tty.Bold msg] in
    Machine.return (Event.screen () ~text)

  (* Formats a term (BIL instruction) for printing on the screen.
     If the user is viewing multiple lines at once, then we want to
     bold the active term, and put a little arrow by it, to indicate
     that it's the current line. Also, if another term has a breakpoint
     associated with it, we want to put a little "b" next to it in
     multiline mode, to indicate that there's a breakpoint there. *)
  let build_output (term : t) (active_tid : Tid.t) (is_multiline : bool)
      : Ui.output Machine.t =

    (* Is this term (BIL instruction) the active term that the user 
       is examining? If so, we want to add a little arrow next to it
       and make it bold if we're showing multiple lines. *)
    if Tid.(term.tid = active_tid) then
      let prefix = if is_multiline then "-> " else "" in
      let style = if is_multiline then Tty.Bold else Tty.Plain in
      let s = Printf.sprintf "%s%s" prefix (string_of term) in
      Machine.return (Ui.mk_output s ~color ~style)

    (* If this term (BIL instruction) is not the active term that the user
       is examining, but it is a breakpoint, we want to add a little "b"
       next to it, to indicate that there's a breakpoint there. *)
    else
      let* is_breakpoint = Cursor.is_break term.tid in
      let prefix = match (is_multiline, is_breakpoint) with
        | (true, true) -> " b "
        | (true, false) -> "   "
        | _ -> ""
        in
      let s = Printf.sprintf "%s%s" prefix (string_of term) in
      Machine.return (Ui.mk_output s ~color)

  (* Generates a screen that displays the current term (BIL instruction)
     along with the nearest +/- [n] other terms (BIL instructions). *) 
  let show_n ?prompt:(prompt=None) ?handler:(handler=None) (n : int)
      : event Machine.t =

    (* Select the relevant terms (BIL instructions) the debugger's
       cursor is pointing at. *)
    let* tid = Cursor.get_tid_exn () in
    let* b = Cursor.get_blk_exn () in
    let terms = term_in tid b ~with_nearest:n in

    (* Construct pretty/formatted versions of the selected terms 
       for display. *)
    let is_multiline = (List.length terms) > 1 in
    let acc = Machine.return([]) in
    let* text = List.fold terms ~init:acc ~f:(fun acc t ->
      let* acc' = acc in
      let* output = build_output t tid is_multiline in
      Machine.return (List.append acc' [output])) in

    (* Put it all together into a screen. *)
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Generates a screen that displays the BIL instruction the debugger's
     cursor is pointing at. If [~with_nearest="3"] is specified, the nearest
     +/- 3 surrounding BIL instructions will also be displayed.
     Why does [~with_nearest] take a string instead of a number? The reason
     is that this value is specified by the user, so it comes in as a string.
     This function has error handling, to ensure that the value is a positive
     integer. If it is not, this function will return an error screen. *)
  let show ?prompt:(prompt=None) ?handler:(handler=None) 
      ?with_nearest:(nearest=None) () : event Machine.t =

    (* If [nearest] was never set, get the number from the cursor,
       and show that many terms (BIL instructions). *)
    match nearest with
    | None ->
      begin
        let* n = Cursor.get_show_nearest () in
        show_n n ~prompt ~handler
      end

    (* Otherwise, the user provided a number. Since the user entered it,
       it's a string. Try to convert it to an integer. *)
    | Some num ->
      begin
        match int_of_string_opt num with

        (* If that fails, return an error screen. *)
        | None ->
          begin
            let msg = Printf.sprintf "Invalid: '%s' must be an int" num in
            let text = [Ui.mk_output ~color:Tty.Red msg] in
            Machine.return (Event.screen () ~text ~prompt ~handler)
          end

        (* If we get an integer, we can move on. *)
        | Some n ->
          begin

            (* If the integer isn't positive, return an error screen. *)
            if n < 0 then
              let msg = Printf.sprintf "Invalid: '%s' must be positive" num in
              let text = [Ui.mk_output ~color:Tty.Red msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)

            (* If we got a positive integer, we can move on. *)
            else
              show_n n ~prompt ~handler

          end

      end

  (* Set the number of +/- nearest other terms (BIL instructions) to always
     display when displaying a term. *)
  let always_show ?prompt:(prompt=None) ?handler:(handler=None) 
      (nearest : string) : event Machine.t =

    (* Try to convert [nearest] into an integer. *) 
    match int_of_string_opt nearest with

    (* If that fails, return an error screen. *)
    | None ->
      begin
        let msg = Printf.sprintf "Invalid: '%s' must be an int" nearest in
        let text = [Ui.mk_output ~color:Tty.Red msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* If we get an integer, we can move on. *)
    | Some n ->
      begin

        (* If the integer isn't positive, return an error screen. *)
        if n < 0 then
          let msg = Printf.sprintf "Invalid: '%s' must be positive" nearest in
          let text = [Ui.mk_output ~color:Tty.Red msg] in
          Machine.return (Event.screen () ~text ~prompt ~handler)

        (* If we got a positive integer, we can move on. Here we just
           need to tell the cursor the number it should always show,
           then we can show that amount. *)
        else
          let* _ = Cursor.set_show_nearest n in
          show_n n ~prompt ~handler

      end

end
