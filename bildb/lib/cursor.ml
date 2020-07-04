(** Implements {!Cursor}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

(* Encapsulates the data that the cursor keeps. *)
module Data = struct

  (* The debugger can move the cursor in step or next mode. In step mode,
     it goes one instruction at a time. In next mode, it skips
     to the next block or breakpoint. *)
  type mode = Step | Next

  (* The debugger can move its cursor forwards or backwards in the program. *)
  type direction = Forward | Backward

  (* A list of TIDs that have breakpoints. *)
  type breaks = Tid.Set.t

  (* Keep all the info in this record. *)
  type t = { 
    blk : Blk.t option;         (* The current block *) 
    tid : Tid.t option;         (* The current TID *)
    was_just_visited : bool;    (* Cursor was just at the current TID? *)
    just_reached_start : bool;  (* Cursor just backed up to program start? *)
    mode : mode;                (* Move in step mode or next mode *)
    direction : direction;      (* Move forward or backward *)
    breaks : breaks;            (* All TIDs with breakpoints *)
    show_nearest : int;         (* Num nearest BIL instructions to show *) 
    last_cmd : Ui.input option; (* The last command the user entered *)
  }

  let empty = { 
    blk = None; 
    tid = None;
    was_just_visited = false;
    just_reached_start = false;
    mode = Step;
    direction = Forward; 
    breaks = Tid.Set.empty;
    show_nearest = 0;
    last_cmd = None;
  }

  let blk t = t.blk
  let tid t = t.tid
  let was_just_visited t = t.was_just_visited
  let just_reached_start t = t.just_reached_start
  let mode t = t.mode
  let direction t = t.direction
  let breaks t = t.breaks
  let show_nearest t = t.show_nearest
  let last_cmd t = t.last_cmd
  let with_blk t blk = { t with blk }
  let with_tid t tid = { t with tid }
  let with_was_just_visited t was_just_visited = { t with was_just_visited }
  let with_just_reached_start t just_reached_start = 
    { t with just_reached_start }
  let with_break t tid = { t with breaks = Tid.Set.add t.breaks tid }
  let without_break t tid = { t with breaks = Tid.Set.remove t.breaks tid }
  let with_mode t mode = { t with mode }
  let with_direction t direction = { t with direction }
  let with_show_nearest t show_nearest = { t with show_nearest }
  let with_last_cmd t last_cmd = { t with last_cmd }

  let set_step_mode t = with_mode t Step
  let set_next_mode t = with_mode t Next
  let is_step_mode t = match t.mode with
    | Step -> true
    | Next -> false

  let set_forward t = with_direction t Forward
  let set_backward t = with_direction t Backward
  let is_forward t = match t.direction with
    | Forward -> true
    | Backward -> false

  let is_break t tid = Tid.Set.mem t.breaks tid
  let list_of_breaks t = Tid.Set.to_list t.breaks

  let data : t Primus.Machine.State.t =
    Primus.Machine.State.declare
      ~uuid:"fa4bc283-8531-425d-8f61-48f090a92093"
      ~name:"data"
      (fun _ -> empty)

end

(* This functor makes a module that has getters/setters for the above data.
   It's very tedious to keep getting/putting data in the machines' global
   state, so this module handles that and lets callers do stuff in one
   function call. *)
module Make (Machine : Primus.Machine.S) = struct
  open Machine.Let_syntax

  let get () = Machine.Global.get Data.data

  let get_blk () : Blk.t option Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.blk data)

  let get_blk_exn () : Blk.t Machine.t =
    let%bind blk = get_blk () in
    let b = Option.value_exn blk in
    Machine.return (b)

  let set_blk (b : Blk.t option) : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_blk data b in
    Machine.Global.put Data.data data' 

  let get_tid () : Tid.t option Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.tid data)

  let get_tid_exn () : Tid.t Machine.t =
    let%bind tid = get_tid () in
    let tid' = Option.value_exn tid in
    Machine.return (tid')

  let set_tid (tid : Tid.t option) : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_tid data tid in
    Machine.Global.put Data.data data' 

  let mark_just_visited () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_was_just_visited data true in
    Machine.Global.put Data.data data'

  let mark_not_just_visited () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_was_just_visited data false in
    Machine.Global.put Data.data data'

  let was_just_visited () : bool Machine.t = 
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.was_just_visited data)

  let mark_just_reached_start () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_just_reached_start data true in
    Machine.Global.put Data.data data'

  let mark_didnt_just_reach_start () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_just_reached_start data false in
    Machine.Global.put Data.data data'

  let just_reached_start () : bool Machine.t = 
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.just_reached_start data)

  let set_step_mode () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.set_step_mode data in
    Machine.Global.put Data.data data'

  let set_next_mode () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.set_next_mode data in
    Machine.Global.put Data.data data'

  let is_step_mode () : bool Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.is_step_mode data)

  let set_forward () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.set_forward data in
    Machine.Global.put Data.data data'

  let set_backward () : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.set_backward data in
    Machine.Global.put Data.data data'

  let is_forward () : bool Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.is_forward data)

  let get_breaks () : Tid.t list Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.list_of_breaks data)

  let add_break (tid : Tid.t) : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_break data tid in
    Machine.Global.put Data.data data' 

  let remove_break (tid : Tid.t) : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.without_break data tid in
    Machine.Global.put Data.data data' 

  let is_break (tid : Tid.t) : bool Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.is_break data tid)

  let get_show_nearest () : int Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.show_nearest data)

  let set_show_nearest (n : int) : unit Machine.t =
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_show_nearest data n in
    Machine.Global.put Data.data data'

  let get_last_cmd () : Ui.input option Machine.t =
    let%bind data = Machine.Global.get Data.data in
    Machine.return (Data.last_cmd data)

  let set_last_cmd (cmd : Ui.input option) : unit Machine.t = 
    let%bind data = Machine.Global.get Data.data in
    let data' = Data.with_last_cmd data cmd in
    Machine.Global.put Data.data data'

  (* Checks if the provided TID is the first term in the
     block that the cursor is currently moving through. *)
  let is_first_in_block (tid : Tid.t) : bool Machine.t =
    let%bind blk = get_blk () in
    match blk with
    | None -> Machine.return false
    | Some b ->
      begin
        match Term.first def_t b with
        | Some d -> Machine.return (Tid.equal tid (Term.tid d))
        | None ->
          begin
            match Term.first jmp_t b with
            | Some j -> Machine.return (Tid.equal tid (Term.tid j))
            | None -> Machine.return false
          end
      end

  (* Checks if the given TID is a basic block. *)
  let is_block (tid : Tid.t) : bool Machine.t =
    let%bind prog = Machine.gets Project.program in
    match Program.lookup blk_t prog tid with
    | Some _ -> Machine.return true
    | None -> Machine.return false

  (* Checks if the given TID is a subroutine. *)
  let is_subroutine (tid : Tid.t) : bool Machine.t =
    let%bind prog = Machine.gets Project.program in
    match Program.lookup sub_t prog tid with
    | Some _ -> Machine.return true
    | None -> Machine.return false

  (* When the cursor is in next mode, it skips forward/backwards.
     It should stop if the term has a breakpoint set on it, or if it
     is the start of a basic block (or the start of a subroutine).
     This function checks if the TID is any of those. *)
  let is_stopping_point (tid : Tid.t) : bool Machine.t =
    let%bind is_breakpoint = is_break tid in
    if is_breakpoint then Machine.return true
    else
      let%bind is_blk = is_block tid in
      if is_blk then Machine.return true
      else
        let%bind is_first = is_first_in_block tid in
        if is_first then Machine.return true
        else
          let%bind is_sub = is_subroutine tid in
          if is_sub then Machine.return true
          else
            Machine.return false

  (* This function checks if the current Primus machine is the initial,
     global machine that started everything. *)
  let is_initial_machine () : bool Machine.t =
    let%bind cid = Machine.current () in
    let%bind pid = Machine.ancestor [cid] in
    Machine.return (Machine.Id.equal pid Machine.global)

  (* This function updates the cursor's internal state with the given
     TID. This makes the given TID the current TID that the cursor is
     pointing at, and it makes the block that the TID is contained in
     the block that the cursor is going through. *)
  let update (tid : Tid.t) : unit Machine.t =
    let%bind prog = Machine.gets Project.program in
    let%bind () = match Program.parent def_t prog tid with
      | Some b -> set_blk (Some b) 
      | None -> 
        begin
          match Program.parent jmp_t prog tid with
          | Some b -> set_blk (Some b)
          | None -> set_blk None 
        end
      in
    let%bind _ = set_tid (Some tid) in
    Machine.return () 

  (* This function moves the cursor backwards one step in the program.
     To implement backstepping, we spawn a new Machine at each instruction.
     Then, to backstep, we just switch to the current Machine's parent. *)
  let backstep () : unit Machine.t =
    let%bind cid = Machine.current () in
    let%bind pid = Machine.ancestor [cid] in
    Machine.switch pid

  (* Lets the cursor run/move, in whatever mode it is currently in, from the
     given TID. For example, if the cursor is in forwards step mode, then
     it will move forward one term (BIL instruction). If it is in forwards
     next mode, it will move forward until it hits the next breakpoint or
     block. If its in backwards step mode, it will move back one term,
     and if it is in backwards next mode, it will move backward until it
     hits a breakpoint or the start of a basic block. *)
  let rec run_from (tid : Tid.t) : unit Machine.t =

    (* Spawn a new machine. *)
    let%bind pid = Machine.current () in
    let%bind _ = Machine.fork () in
    let%bind cid = Machine.current () in

    (* If we're back in the parent machine, that means the child fork
       has finished, and execution has returned back to this point. *)
    match Machine.Id.equal pid cid with
    | true ->
      begin
        let%bind _ = update tid in

        (* If we're moving forwards, we can run from this TID. *)
        let%bind is_forwards = is_forward () in
        match is_forwards with
        | true -> run_from tid

        (* Otherwise, we're moving backwards. *)
        | false ->
          begin

            (* If we're back to the initial machine, we can start moving
               forward again, in step mode. *) 
            let%bind is_init = is_initial_machine () in
            match is_init with
            | true ->
              begin
                let%bind _ = set_forward () in
                let%bind _ = set_step_mode () in
                let%bind _ = mark_not_just_visited () in
                let%bind _ = mark_just_reached_start () in
                run_from tid
              end

            (* Otherwise, we're not back to the start, and we're supposed
               to be moving backwards. *)
            | false ->
              begin

                (* If we're at a stop point, and we didn't already just
                   stop here, then we should start moving forward again in
                   step mode, which will cause the debugger to stop and let
                   the user step through this term (BIL instruction). *)
                let%bind is_stop = is_stopping_point tid in
                let%bind just_visited = was_just_visited () in
                match is_stop && not just_visited with
                | true ->
                  begin
                    let%bind _ = set_forward () in
                    let%bind _ = set_step_mode () in
                    run_from tid
                  end

                (* Otherwise, we're moving backwards, and we're not at
                   a stopping point that we just visited. *)
                | false ->
                  begin

                    (* Are we in (backward) step mode? If so, go backward
                       one step, and start running forward again. That will
                       cause the debugger to stop and let the user step
                       through the next term (BIL instruction). *)
                    let%bind is_step = is_step_mode () in
                    let%bind _ = mark_not_just_visited () in
                    match is_step with
                    | true ->
                      begin
                        let%bind _ = set_forward () in
                        backstep ()
                      end

                    (* We're not in step mode, and we're moving backwards,
                       so we can just step back one step and let things
                       continue. *)
                    | false -> backstep ()

                  end

              end

          end

      end

    (* We are not back in the parent machine, so we must be in the
       child Machine that was just spawned by the [fork()] function.
       In that case, we can just let the debugger proceed in whatevr
       mode it is in. *)
    | false ->
      begin
        let%bind _ = update tid in
        let%bind _ = mark_just_visited () in 
        Machine.return ()
      end

end
