(** Implements {!Variables}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Env = Primus.Env.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module Event = Ui.Event (Machine)
  open Machine.Let_syntax

  type event = Event.t

  (* Makes a string of the provided value in hex format. *)
  let string_of (v : Value.t) : string =
    let w = Value.to_word v in
    Format.asprintf "%a" Word.pp_hex w

  (* Generates a pretty "key: value" string of a variable. *)
  let val_of (v : Var.t) : string Machine.t =
     let name = Var.to_string v in
     let%bind variable = Env.get v in
     let value = string_of variable in
     let result =
       Printf.sprintf "%s: %s" (Utils.pad name Ui.key_width) value in
     Machine.return (result)

  (* Find a variable by name in the environment, if any. *)
  let find_var (name : string) : Var.t option Machine.t =
    let%bind vars = Env.all in
    let var = Seq.find vars ~f:(fun r -> String.equal (Var.name r) name) in
    Machine.return (var)

  (* Generates a screen that displays the value of a variable. The variable
     is provided as a string (it is the name of the variable that a user
     typed in). If no such variable exists in the environment, then this
     function returns an error screen instead. *)
  let show_var ?prompt:(prompt=None) ?handler:(handler=None) 
      (name : string) : event Machine.t =

    (* If we can't find the variable, return an error screen. *)
    let%bind var = find_var name in
    match var with
    | None ->
      begin
        let msg = Printf.sprintf "No such variable: %s" name in
        let text = [Ui.mk_output ~color:Tty.Red msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* Otherwise make a screen that shows the value. *)
    | Some v ->
      begin
        let%bind value = val_of v in
        let text = [Ui.mk_output ~color:Tty.Green value] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

  (* Generates a screen that displays all general purpose registers
     and their values. *)
  let show_regs ?prompt:(prompt=None) ?handler:(handler=None) () 
      : event Machine.t =

    (* Get the list of GPRs from the architecture. *)
    let%bind arch = Machine.arch in
    let module T = (val target_of_arch arch) in
    let regs = Var.Set.to_list T.CPU.gpr in

    (* Extract each value into a list. *)
    let%bind values =
      List.fold regs ~init:(Machine.return []) ~f:(fun acc r ->
        let%bind value = val_of r in
        let%bind acc' = acc in
        Machine.return (List.append acc' [value])
        ) in

    (* Tabulate the values for pretty printing, and put 'em into a screen. *)
    let lines = Utils.tabulate values Ui.screen_width in
    let text =
      List.map lines ~f:(fun line -> Ui.mk_output ~color:Tty.Green line) in
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Generates a screen that shows all variables in the environment. *)
  let show_all ?prompt:(prompt=None) ?handler:(handler=None) () 
      : event Machine.t =

    (* Get the variables from the environment. *)
    let%bind variables = Env.all in
    let vars = Seq.to_list variables in

    (* Extract each value into a list. *)
    let%bind values =
      List.fold vars ~init:(Machine.return []) ~f:(fun acc v ->
        let%bind value = val_of v in
        let%bind acc' = acc in
        Machine.return (List.append acc' [value])
        ) in

    (* Tabulate the values for pretty printing, and put 'em into a screen. *)
    let lines = Utils.tabulate values Ui.screen_width in
    let text =
      List.map lines ~f:(fun line -> Ui.mk_output ~color:Tty.Green line) in
    Machine.return (Event.screen () ~text ~prompt ~handler)

  (* Sets a given variable to a given value, and then generates a screen
     showing the new value. The variable name and value are given as strings,
     which a user typed in. If the variable doesn't exist, or the value
     is not in the proper hex format, this function will return an
     error screen instead. *)
  let set_var ?prompt:(prompt=None) ?handler:(handler=None) (name : string)
      (value : string) : event Machine.t =

    (* If the variable doesn't exist, return an error screen. *)
    let%bind var = find_var name in
    match var with
    | None ->
      begin
        let msg = Printf.sprintf "No such variable: %s" name in
        let text = [Ui.mk_output ~color:Tty.Red msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* If we get a variable, we can proceed. *)
    | Some v ->
      begin
        let%bind arch = Machine.arch in
        let module T = (val target_of_arch arch) in
        let bits = Utils.int_of_size (Arch.addr_size arch) in

        (* If we can't convert the value into a binary word, return an
           error screen. *)
        match Utils.word_of value ~bits with
        | None ->
          begin
            let msg = Printf.sprintf "Invalid hex value: %s" value in
            let text = [Ui.mk_output ~color:Tty.Red msg] in
            Machine.return (Event.screen () ~text ~prompt ~handler)
          end

        (* If we got a binary word, set the variable to that value, and
           then generate a screen that shows the new value. *)
        | Some w ->
          begin
            let%bind w_value = Value.of_word w in
            let%bind _ = Env.set v w_value in
            show_var name ~prompt ~handler
          end

      end

end
