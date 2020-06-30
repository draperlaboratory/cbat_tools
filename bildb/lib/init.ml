(** Implements {!Init}. *)

open Core_kernel
open Bap.Std

module Data = State.Data

(* This module is responsible for breaking up an init file into tokens.
   See {!Init} for a description of init files. *) 
module Lexer = struct

  (* The different kinds of tokens, including errors. *)
  type token =
    | Variables of int
    | Locations of int
    | Key of (int * string) 
    | Value of (int * string)
    | Error of (int * string)

  (* Tokenizing returns a sequence of tokens. *)
  type t = token list

  (* For pretty printing, especially error messages. *)
  let string_of_token (tok : token) : string = 
    match tok with
    | Variables _ -> "Variables"
    | Locations _ -> "Locations"
    | Key (_, s) -> s
    | Value (_, s) -> s
    | Error (l, s) -> Printf.sprintf "Error on line %d. %s" l s

  (* For extracting the line in the init file a token was found in. *)
  let line_of (tok : token) : int =
    match tok with
    | Variables n -> n
    | Locations n -> n
    | Key (n, _) -> n
    | Value (n, _) -> n
    | Error (n, _) -> n

  (* For printing all errors at once. *)
  let string_of_errors (errors : token list) : string =
    let pieces = List.map errors ~f:(fun x ->
      Printf.sprintf "- %s" (string_of_token x)) in
    String.concat pieces ~sep:"\n"

  (* This function takes a line number [n] and a line from an init file,
     and it extracts the tokens in that line. *)
  let tokens_of (n : int) (line : string) : token list =
    let s = String.strip line in

    (* Ignore it if it's a blank line. *)
    if String.length s = 0 then []
    else

      (* It could be a 'Variables:' or 'Locations:' heading. *)
      if String.is_prefix s ~prefix:"Variables:" then [Variables n]
      else
        if String.is_prefix s ~prefix:"Locations:" then [Locations n]
        else

          (* Otherwise, we should have a 'key : value' line. *)
          let pieces = String.split s ~on:':' in
          if List.length pieces <> 2 then
            let msg = 
              Printf.sprintf "Expected 'key : value' but got '%s'" s in
            [Error (n, msg)]
          else
            let pieces' = List.map pieces ~f:String.strip in
            let key = List.nth_exn pieces' 0 in
            let value = List.nth_exn pieces' 1 in
            [Key (n, key); Value (n, value)]

  (* Recursively tokenize each line of the init file. *)
  let rec next ?n:(n=1) (lines : string list) : t =
    match lines with
    | [] -> []
    | x :: xs -> List.append (tokens_of n x) (next ~n:(n + 1) xs)

  (* This function takes a list of lines from an init file,
     and tokenizes the whole thing. If there are any error tokens in the
     resulting sequence of tokens, it returns an error with those messages.
     Otherwise, it returns the sequence of tokens. *)
  let tokenize (lines : string list) : (t, string) Stdlib.result =
    let toks = next lines in
    let errors = List.filter toks ~f:(fun x -> match x with
      | Error _ -> true
      | _ -> false) in
    match List.length errors = 0 with
    | false -> Error (string_of_errors errors)
    | true -> Ok toks

end

(* This module is responsible for taking a list of tokens and turning
   it into a {!Data.t} data structure. *) 
module Parser = struct

  (* When parsing a hex string, it can be in an invalid format. *)
  type word_error =
    | Invalid_hex of string

  (* Parse errors have a line number (an [int]) where they occur, 
     and a message (a [string] describing the error. *) 
  type error =
    | Hex_error of int * string
    | Section_error of int * string

  (* Some shortcuts for various result types. *)
  type word_result = (Word.t, word_error) Stdlib.result
  type vars_result = (Data.variable list, error) Stdlib.result
  type locs_result = (Data.location list, error) Stdlib.result
  type parse_result = (Data.t, error) Stdlib.result

  (* For pretty printing parse errors. *)
  let error_msg (e : error) : string =
    match e with
    | Hex_error (n, msg) ->
      Printf.sprintf "Error on line %d: invalid hex '%s'\n" n msg
    | Section_error (n, msg) ->
      Printf.sprintf "Error on line %d: %s\n" n msg

  (* [word_of "0x0000ff"] attempts to convert ["0x0000ff"] into a [Word.t].
     If it's successful, it returns the [Word.t].
     If not, it returns a [word_error]. *)
  let word_of ?bits:(bits=64) ?sign:(sign="u") (s : string) : word_result =
    if String.prefix s 2 <> "0x" then Error (Invalid_hex s)
    else 
      try
        let subject = Printf.sprintf "%s:%d%s" s bits sign in
        Ok (Word.of_string subject)
      with _ -> Error (Invalid_hex s)

  (* This function recursively eats up and parses tokens that specify
     variables and the values they should be initialized as. If it
     succeeds, it returns a {Data.variable list}. Otherwise, 
     it returns a parse error. *)
  let rec vars_from ?acc:(acc=[]) (tokens : Lexer.t) : vars_result =
    if List.length tokens = 0 then Ok acc
    else
      let tok_1 = List.nth_exn tokens 0 in
      let tok_2 = List.nth_exn tokens 1 in
      let the_rest = List.drop tokens 2 in
      let line = Lexer.line_of tok_2 in
      let key = Lexer.string_of_token tok_1 in
      let value = Lexer.string_of_token tok_2 in
      match word_of value with
      | Error e -> Error (Hex_error (line, value))
      | Ok w -> 
        let new_acc = List.append [Data.mk_variable key w] acc in
        vars_from ~acc:new_acc the_rest

  (* This function recursively eats up and parses tokens that specify
     addresses and the values that should initially be stored in them.
     If it succeeds, it returns a {Data.location list}. Otherwise,
     it returns a parse error. *)
  let rec locs_from ?acc:(acc=[]) (tokens : Lexer.t) : locs_result =
    if List.length tokens = 0 then Ok acc
    else
      let tok_1 = List.nth_exn tokens 0 in
      let tok_2 = List.nth_exn tokens 1 in
      let address = Lexer.string_of_token tok_1 in
      let value = Lexer.string_of_token tok_2 in
      match word_of address with
      | Error e -> Error (Hex_error (Lexer.line_of tok_1, address))
      | Ok a ->
        begin 
          match word_of value with
          | Error e -> Error (Hex_error (Lexer.line_of tok_2, value))
          | Ok w ->
            begin 
              let the_rest = List.drop tokens 2 in
              let new_acc = List.append [Data.mk_location a w] acc in
              locs_from ~acc:new_acc the_rest
            end
        end

  (* This function parses a sequence of tokens and converts it into a
     {Data.t} data structure. If parsing fails, it returns a parse error. *) 
  let rec parse ?acc:(acc=Data.empty) (tokens : Lexer.t) : parse_result =
    if List.length tokens = 0 then Ok acc
    else
      let head = List.hd_exn tokens in
      let tail = List.tl_exn tokens in
      match head with

      (* If we're at the start of a 'Variables' section, break off all the 
         tokens that come next until the start of a 'Locations' section or
         the end of the file. Then parse those tokens into variable specs. *)
      | Lexer.Variables _ -> 
        begin
          let var_tokens, the_rest = List.split_while tail ~f:(fun x ->
            match x with
            | Lexer.Locations _ -> false
            | _ -> true) in
          let r = vars_from var_tokens in
          match r with
          | Error e -> Error e
          | Ok vars -> 
            let new_acc = Data.with_variables acc vars in
            parse ~acc:new_acc the_rest
        end

      (* If we're at the start of a 'Locations' section, break off all the
         tokens that come next until the start of a 'Variables' section or
         the end of the file. Then parse those tokens into location specs. *)
      | Lexer.Locations _ ->
        begin
          let loc_tokens, the_rest = List.split_while tail ~f:(fun x ->
            match x with
            | Lexer.Variables _ -> false
            | _ -> true) in
          let r = locs_from loc_tokens in
          match r with
          | Error e -> Error e
          | Ok locs ->
            let new_acc = Data.with_locations acc locs in
            parse ~acc:new_acc the_rest
        end

      (* We only expect section headings. *)
      | _ ->
        begin
          let msg = "expected 'Variables:' or 'Locations:' section" in
          Error (Section_error (Lexer.line_of head, msg)) 
        end

end

(* This function takes a filepath and returns the lines in it. *)
let contents (filepath : string) : (string list, exn) Stdlib.result =
  try 
    let lines = In_channel.read_lines filepath in
    Ok lines
  with e -> Error e

(* This is the main function in the module. See {!Init.from_file}. *)
let from_file (filepath : string) : (Data.t, string) Stdlib.result  =
  let r = contents filepath in
  match r with
  | Ok data -> 
    begin
      let r = Lexer.tokenize data in
      match r with
      | Error e -> Error e
      | Ok tokens ->
        begin
          let r' = Parser.parse tokens in
          match r' with
          | Error e -> Error (Parser.error_msg e)
          | Ok result -> Ok result
        end
    end
  | Error e -> 
    begin
      match e with
      | Sys_error msg -> Error msg
      | _ -> Error (Exn.to_string e)
    end
