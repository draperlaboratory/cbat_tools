(** Implements {!Locations}. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std

module Ui = Bildb_ui
module Utils = Bildb_utils
module Tty = Bildb_tty

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)
  module Mem = Primus.Memory.Make (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  type event = Event.t

  (* Stringify an address/word pair. *)
  let pretty (a : Addr.t) (w : Word.t) : string =
    let a_str = Utils.string_of a in
    let w_str = Utils.string_of w in
    Printf.sprintf "%s: %s" (Utils.pad a_str Ui.key_width) w_str

  (* Get [num_words] number of consecutive addresses, starting at [addr]. *)
  let addresses_from ?addr_size:(addr_size=64) ?num_words:(num_words=1)
      (addr : Addr.t) : Word.t Core_kernel.List.t =
    List.init num_words ~f:(fun i ->
      let offset = Word.of_int ~width:addr_size i in
      Word.(+) addr offset)

  (* Read the specified number of words stored in memory, starting at
     the specified address. *)
  let read_loc ?addr_size:(addr_size=64) ?num_words:(num_words=1)
      (addr : Addr.t) : ((Word.t * Word.t) Core_kernel.List.t) Machine.t =
    let acc = Machine.return [] in
    let addresses = addresses_from addr ~addr_size ~num_words in
    List.fold addresses ~init:acc ~f:(fun acc addr ->
      let* words = acc in
      let* w = Mem.load addr in
      let acc' = List.append words [(addr, w)] in
      Machine.return acc')

  (* Return all addresses that aren't mapped/allocated, starting from
     the given [addr] and proceeding [num_words] bytes. *) 
  let unmapped ?addr_size:(addr_size=64) ?num_words:(num_words=1)
      (addr : Addr.t) : (Word.t Core_kernel.List.t) Machine.t =
    let acc = Machine.return [] in
    let addresses = addresses_from addr ~addr_size ~num_words in
    List.fold addresses ~init:acc ~f:(fun acc addr' ->
      let* words = acc in
      let* is_allocated = Mem.is_mapped addr' in
      let acc' = match is_allocated with
        | true -> words
        | false -> List.append words [addr'] in
      Machine.return acc')

  (* Generates a screen that displays the data stored at a location.
     The [~num_words] specifies how many bytes to read, starting
     from the address [addr]. Both the address and the number of
     words are specified as strings, because the user types them in.
     If the format is not right (if the addres is not a valid hex value
     or the number of words is not a positive integer), this function
     will generate appropriate error screens. If any of the locations
     are unmapped/unallocated, an appropriate error screen will also
     be generated. *)
  let show_locs ?prompt:(prompt=None) ?handler:(handler=None)
      ?num_words:(num_words="1") (addr : string) : event Machine.t =

    (* If we can't convert [~num_words] to an integer,
       return an error screen. *)
    match int_of_string_opt num_words with
    | None ->
      begin
        let msg = Printf.sprintf "Invalid: '%s' must be an int" num_words in
        let text = [Ui.mk_output ~color:Tty.Red msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* If we do get an integer, we can proceed. *)
    | Some num_words ->
      begin

        (* If it's not a positive integer, return an error screen. *)
        if num_words < 0 then
          let msg =
            Printf.sprintf "Invalid: '%d' must be positive" num_words in
          let text = [Ui.mk_output ~color:Tty.Red msg] in
          Machine.return (Event.screen () ~text ~prompt ~handler)

        (* Otherwise, we can proceed. *)
        else
          let* arch = Machine.arch in
          let addr_size = Utils.int_of_size (Arch.addr_size arch) in

          (* If we can't convert the provided address into a binary word,
             return an error screen. *)
          match Utils.word_of addr ~bits:addr_size with
          | None ->
            begin
              let msg = Printf.sprintf "Invalid hex value: %s" addr in
              let text = [Ui.mk_output ~color:Tty.Red msg] in
              Machine.return (Event.screen () ~text ~prompt ~handler)
            end

          (* If we get a hex, we can proceed. *)
          | Some addr' ->
            begin

              (* Are any addresses we're going to road unmapped?
                 If not, we can read them and display them. *)
              let* addrs = unmapped addr' ~addr_size ~num_words in
              match addrs with
              | [] ->
                begin      
                  let* words = read_loc addr' ~addr_size ~num_words in
                  let words_pretty =
                    List.map words ~f:(fun w -> pretty (fst w) (snd w)) in
                  let lines = Utils.tabulate words_pretty Ui.screen_width in
                  let text = List.map lines ~f:(fun line ->
                    Ui.mk_output ~color:Tty.Green line) in
                  Machine.return (Event.screen () ~text ~prompt ~handler)
                end

              (* If some addresses aren't mapped, alert the user. 
                 Trying to read them would result in a page fault,
                 and cause Primus to exit. *)
              | _ ->
                begin
                  let msg =
                    "These addresses are unmapped and cannot be read from:" 
                    in
                  let words_pretty =
                    List.map addrs ~f:(fun w -> Utils.string_of w) in
                  let lines = Utils.tabulate words_pretty Ui.screen_width in
                  let lines' = List.map lines ~f:(fun line ->
                    Ui.mk_output ~color:Tty.Red line) in
                  let text = List.append
                    [Ui.mk_output ~color:Tty.Red msg]
                    lines' in
                  Machine.return (Event.screen () ~text ~prompt ~handler)
                end

            end

      end

  (* Stores a value at an address, and generates a screen saying this
     happened. The address and the value are provided as strings here,
     because the user types them in. If they are not in the right format,
     this function will generate appropriate error screens. If any of the
     addresses are not mapped, this function also generates an error screen
     displaying which addresses are not mapped. *) 
  let set_loc ?prompt:(prompt=None) ?handler:(handler=None)
      (addr : string) (value : string) : event Machine.t =
    let* arch = Machine.arch in
    let addr_size = Utils.int_of_size (Arch.addr_size arch) in
    let word_size = 8 in

    (* If we can't convert the provided address into a binary word,
       return an error screen. *)
    match Utils.word_of addr ~bits:addr_size with
    | None ->
      begin
        let msg = Printf.sprintf "Invalid address hex value: %s" addr in
        let text = [Ui.mk_output ~color:Tty.Red msg] in
        Machine.return (Event.screen () ~text ~prompt ~handler)
      end

    (* If we got an address, we can go on. *)
    | Some addr' ->
      begin

        (* If we can't convert the provided value into a binary word,
           return an error screen. *)
        match Utils.word_of value ~bits:word_size with
        | None ->
          begin
            let msg = Printf.sprintf "Invalid hex value: %s" addr in
            let text = [Ui.mk_output ~color:Tty.Red msg] in
            Machine.return (Event.screen () ~text ~prompt ~handler)
          end

        (* If we got a binary word for the value, we can move on. *)
        | Some value' ->
          begin

              (* Allocate the memory at the specified address (if needed),
                 then store the provided value there. *)
              let* is_mapped = Mem.is_mapped addr' in
              let* _ = if is_mapped
                then Machine.return ()
                else Mem.allocate addr' 1
                in
              let* _ = Mem.store addr' value' in
              show_locs addr ~prompt ~handler ~num_words:"1"

          end

      end

end
