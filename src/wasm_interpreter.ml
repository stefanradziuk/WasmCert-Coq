(** Main file for the Wasm interpreter **)

(* TODO: refactor *)

let instantiate_interpret verbosity interactive error_code_on_crash m name depth =
  let open Output in
  let open Execute.Interpreter in
  let open Out in
  let* store_inst_exps =
    ovpending verbosity stage "instantiation" (fun _ ->
      match interp_instantiate_wrapper m with
      | None -> Error "instantiation error"
      | Some (store_inst_exps, _) -> OK store_inst_exps) in
  if interactive then Obj.magic (* TODO FIXME *) (OK (Execute.repl store_inst_exps name depth))
  else Execute.interpret verbosity error_code_on_crash store_inst_exps name depth

(** Main function *)
let process_args_and_run verbosity text no_exec interactive error_code_on_crash func_name depth srcs =
  let open Output in
  try
    (** Preparing the files. *)
    let files =
      List.map (fun dest ->
        if not (Sys.file_exists dest) || Sys.is_directory dest then
          invalid_arg (Printf.sprintf "No file %s found." dest)
        else
          let in_channel = open_in_bin dest in
          let rec aux acc =
            match try Some (input_char in_channel)
                  with End_of_file -> None with
            | Some c -> aux (c :: acc)
            | None ->
              close_in in_channel;
              List.rev acc in
          aux []) srcs in
    (** Parsing. *)
    let open Out in
    let* m =
      ovpending verbosity stage "parsing" (fun _ ->
        if text then
          Error "Text mode not yet implemented."
        else
          match (* TODO: Use [Shim]. *) Extract.run_parse_module (List.concat files) with
          | None -> Error "syntax error"
          | Some m -> OK m) in
    (** Running. *)
    if no_exec then
      (debug_info verbosity stage (fun _ ->
        "skipping interpretation because of --no-exec.\n") ;
       OK (Execute.Interpreter.pure ()))
    else instantiate_interpret verbosity interactive error_code_on_crash m func_name depth
  with Invalid_argument msg -> Error msg

(** Similar to [process_args_and_run], but differs in the output type. *)
let process_args_and_run_out verbosity text no_exec interactive error_code_on_crash func_name depth srcs =
  process_args_and_run verbosity text no_exec interactive error_code_on_crash func_name depth srcs
  |> Output.Out.convert

(** Command line interface *)

open Cmdliner

let verbosity =
  let mk v l doc =
    let doc = "Verbosity level: " ^ doc in
    (v, Arg.info l ~doc) in
  Arg.(value & vflag Output.result Output.[
      mk none ["vn"; "nothing"] "Print nothing" ;
      mk result ["vr"; "result"] "Only print the result" ;
      mk stage ["vs"; "stage"] "Also print stage" ;
      mk intermediate ["vi"; "intermediate"] "Also print intermediate states, without stores" ;
      mk store ["va"; "all"; "store"] "Also print stores" ;
    ])

let text =
  let doc = "Read text format." in
  Arg.(value & flag & info ["text"] ~doc)

let no_exec =
  let doc = "Stop before executing (only go up to typechecking)." in
  Arg.(value & flag & info ["no-exec"] ~doc)

let interactive =
  let doc = "Interactive execution." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)

let error_code_on_crash =
  let doc = "Return an error code on crash." in
  Arg.(value & flag & info ["E"; "error-if-crash"] ~doc)

let func_name =
  let doc = "Name of the Wasm function to run." in
  Arg.(required & pos ~rev:true 1 (some string) None & info [] ~docv:"NAME" ~doc)

let depth =
  let doc = "Depth to which to run the Wasm evaluator." in
  Arg.(required & pos ~rev:true 0 (some int) None & info [] ~docv:"DEPTH" ~doc)

let srcs =
  let doc = "Source file(s) to interpret." in
  Arg.(non_empty & pos_left ~rev:true 1 file [] & info [] ~docv:"FILE" ~doc)

let cmd =
  let doc = "Interpret WebAssembly files" in
  let man_xrefs = [] in
  let exits = Term.default_exits in
  let man =
    [ `S Manpage.s_bugs;
      `P "Report them at https://github.com/WasmCert/WasmCert-Coq/issues"; ]
  in
  (Term.(ret (const process_args_and_run_out $ verbosity $ text $ no_exec $ interactive $ error_code_on_crash $ func_name $ depth $ srcs)),
   Term.info "wasm_interpreter" ~version:"%%VERSION%%" ~doc ~exits ~man ~man_xrefs)

let () = Term.(exit @@ eval cmd)

