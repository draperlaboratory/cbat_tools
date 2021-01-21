(** Implements {!Position}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Debug = Debugger.Make (Machine)
  module UI = Ui.Make (Machine)
  module Cursor = Cursor.Make (Machine)
  module Whole_program = Whole_program.Make (Machine)
  module Subroutine = Subroutines.Make (Machine)
  module Block = Blocks.Make (Machine)
  module Halts = Halts.Make (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  let prompt = Utils.prompt
  let handler = Some Debug.main_loop

  (* This function is triggered when Primus enters a subroutine. 
     Here we render a screen to display info about the subroutine. *)
  let enter_sub (s : Sub.t) : unit Machine.t =
    let tid = Term.tid s in
    let* _ = Cursor.update tid in
    let* screen = Subroutine.enter s in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when Primus enters an argument term,
     i.e., an argument to a subroutine. Here we render a screen that
     displays info about the argument. *)
  let enter_arg (a : Arg.t) : unit Machine.t =
    let* screen = Subroutine.arg a in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when Primus enteres a basic block.
     When a user skips forward/backward, they skip ahead/backwards to the
     nearest breakpoint or basic block. Since this is a basic block,
     we want to make sure that the debugger's cursor stops here. We do
     that by setting the cursor to step mode, which tells it to let the
     user step through this instruction themselves. Then we render a
     screen that displays info about the basic block. *)
  let enter_blk (b : Blk.t) : unit Machine.t =
    let tid = Term.tid b in
    let* _ = Cursor.set_step_mode () in
    let* _ = Cursor.update tid in
    let* screen = Block.enter () in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when Primus enters a jump. If the cursor
     is in "next mode" (skip ahead/backwards mode) rather than "step mode,"
     the cursor will move on to the next term. If not, this function will
     render a screen that displays the term. *)
  let enter_jmp (j : Jmp.t) : unit Machine.t =

    (* Let the debugger's cursor run, starting at this point.
       If the cursor is not in "step mode", it will skip past this term, 
       and it will move forward/backward to the next term, depending on
       whether it's in forward/backward mode. *)
    let tid = Term.tid j in
    let* _ = Cursor.run_from tid in

    (* If we're at the start of the program, render a screen saying so. *)
    let* screen = Whole_program.start () ~prompt:None ~handler:None in
    let* _ = UI.render screen in

    (* If the cursor has actually stopped here, so the user can step
       through this term, then display the screen for that. *)
    let* is_step = Cursor.is_step_mode () in
    let* is_stop = Cursor.is_stopping_point tid in
    if is_step || is_stop then
      let* screen = Block.show () ~prompt ~handler in
      let* _ = UI.render screen in
      Machine.return ()
    else
      Machine.return ()  

  (* This function is triggered when Primus enters a def. If the cursor
     is in "next mode" (skip ahead/backwards mode) rather than "step mode,"
     the cursor will move on to the next term. If not, this function will
     render a screen that displays the term. *)
  let enter_def (d : Def.t) : unit Machine.t =

    (* Let the debugger's cursor run, starting at this point.
       If the cursor is not in "step mode", it will skip past this term, 
       and it will move forward/backward to the next term, depending on
       whether it's in forward/backward mode. *)
    let tid = Term.tid d in
    let* _ = Cursor.run_from tid in

    (* If we're at the start of the program, render a screen saying so. *)
    let* screen = Whole_program.start () ~prompt:None ~handler:None in
    let* _ = UI.render screen in

    (* If the cursor has actually stopped here, so the user can step
       through this instruction, then display the screen for that. *)
    let* is_step = Cursor.is_step_mode () in
    let* is_stop = Cursor.is_stopping_point tid in
    if is_step || is_stop then
      let* screen = Block.show () ~prompt ~handler in
      let* _ = UI.render screen in
      Machine.return ()
    else
      Machine.return ()  

  (* This function is triggered when a Primus machine halts.
     Here we display a screen saying this. *)
  let halting () =
    let* cid = Machine.current () in
    let* screen = Halts.halt cid ~prompt ~handler in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when an interrupt is signaled.
     Here we display a screen saying as much. *)
  let interrupt n =
    let* cid = Machine.current () in
    let* screen = Halts.interrupt cid n ~prompt ~handler in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when a div-by-zero trap is signaled.
     Here we display a screen saying as much. *)
  let division_by_zero () =
    let* cid = Machine.current () in
    let* screen = Halts.div_by_zero () ~prompt ~handler in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when an exception is raised in a machine.
     Here we display a screen saying this, displaying the exception. *)
  let exn_raised e =
    let* cid = Machine.current () in
    let* screen = Halts.exn_raised cid e in
    let* _ = UI.render screen in
    Machine.return ()

  (* This function is triggered when Primus finishes.
     Here we display a screen saying as much. *)
  let finished () =
    let* screen = Halts.fini () ~prompt ~handler in
    let* _ = UI.render screen in
    Machine.return ()

  (* Subscribes to the appropriate Primus events. *)
  let init () =
    let open Machine.Syntax in
    Machine.sequence [
      Primus.Interpreter.enter_sub >>> enter_sub;
      Primus.Interpreter.enter_arg >>> enter_arg;
      Primus.Interpreter.enter_blk >>> enter_blk;
      Primus.Interpreter.enter_jmp >>> enter_jmp;
      Primus.Interpreter.enter_def >>> enter_def;
      Primus.Interpreter.halting >>> halting;
      Primus.Interpreter.interrupt >>> interrupt;
      Primus.Interpreter.division_by_zero >>> division_by_zero;
      Primus.Machine.exn_raised >>> exn_raised;
      Primus.System.fini >>> finished;
    ]

end
