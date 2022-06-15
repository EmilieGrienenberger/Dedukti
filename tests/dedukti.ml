module Command = struct
  type t = Dkcheck | Dkmeta | Dkpretty

  let path = function
    | Dkcheck -> ("./dk.native", fun args -> "check" :: args)
    | Dkmeta -> ("./dk.native", fun args -> "meta" :: args)
    | Dkpretty -> ("./dk.native", fun args -> "beautify" :: args)
end

let remove_dkos () =
  Process.spawn "find" ["."; "-name"; "*.dko"; "-type"; "f"; "-delete"]
  |> Process.check

(* - [preprocess] is called at the beginning of the test. It can be
   used to handle dependencies that need to be type checked.

   - [postprocess] is called on the output generated by a regression
   test if the test is not expected to fail (see [error] parameter).

   - [regression] contains the filename of the regression, [None]
   otherwise.

   - [error] is contains the error code if the test is expected to
   fail, [None] otherwise.

   - [title] is the tile of the test.

   - [tags] are the tags of the test.

   - [filename] is the filename on which the test is run.

   - [command] is the command that should be run such as [dkcheck],
   [dkmeta], ...

   - [arguments] are the various arguments (as a list of strings)
   given to the command. *)

let run ?(preprocess = return) ?(postprocess = fun _ -> return ()) ~regression
    ~error ~title ~tags ~filename command arguments =
  let regression_output_path = "tests/tezt/_regressions" in
  let register f =
    match regression with
    | None -> Test.register ~__FILE__:filename ~title ~tags f
    | Some output_file ->
        Regression.register ~__FILE__:filename ~output_file
          ~regression_output_path ~title ~tags f
  in
  register (fun () ->
      let* () = preprocess () in
      let output_options =
        (* --no-color: Do not print color characters for regression output. *)
        if regression <> None then ["--no-color"; "-q"]
        else if Cli.options.log_level = Cli.Report then ["-q"]
        else if Cli.options.log_level = Cli.Debug then ["-d"; "montru"]
        else if Cli.options.log_level = Cli.Info then ["-d"; "n"]
        else []
      in
      let arguments = output_options @ arguments in
      let output_acc = ref [] in
      let hooks =
        if regression <> None then
          (* We record the standard output so that we can postprocess it. *)
          Some
            Regression.
              {
                hooks with
                on_log =
                  (fun line ->
                    output_acc := line :: !output_acc;
                    hooks.on_log line);
              }
        else if Cli.options.log_level = Cli.Info then
          (* In [Info] mode, we have to tell to Tezt which lines need to
             be reported. By default, in [Debug] mode, Tezt will report
             all the logged lines. Nothing should be printed in [Report]
             mode. *)
          Some
            Process.
              {
                on_log = (fun line -> Log.info "%s" line);
                on_spawn =
                  (fun command arguments ->
                    let message = Log.quote_shell_command command arguments in
                    Log.info ~color:Log.Color.bold ~prefix:command "%s" message);
              }
        else None
      in
      let path, carg = Command.path command in
      let process = Process.spawn ?hooks path (carg (arguments @ [filename])) in
      match error with
      | None ->
          let* () = Process.check process in
          postprocess (List.rev !output_acc)
      | Some (`Code code) ->
          (* We check the process returned on [stderr] the expected error code *)
          Process.check_error
            ~msg:Base.(rex (sf "[ERROR CODE:%d]" code))
            process
      | Some `System ->
          Process.check_error ~msg:(Base.rex "[ERROR CODE:SYSTEM]") process)

let title ~action ~result ~options filename =
  let options_str = String.concat ", " options in
  let basename = Filename.basename filename in
  match options with
  | [] -> Format.asprintf "%s '%s' %s" action basename result
  | [option] ->
      Format.asprintf "%s '%s' %s with '%s'" action basename result option
  | _ :: _ ->
      Format.asprintf "%s '%s' %s with '%s'" action basename result options_str

module Check = struct
  type argument = Eta | Import of string

  let mk_argument = function Eta -> ["--eta"] | Import path -> ["-I"; path]

  let tag_of_argument = function Eta -> "eta" | Import _ -> "import"

  let run ~regression ~error ~filename arguments =
    let tags = List.map tag_of_argument arguments in
    let arguments = List.map mk_argument arguments |> List.concat in
    let result = if error <> None then "fails" else "succeeds" in
    let result_tag = if error <> None then "ko" else "ok" in
    let title = title ~action:"check" ~result ~options:tags filename in
    let tags = "dkcheck" :: result_tag :: tags in
    let regression =
      if regression then Some (String.concat "_" (filename :: tags)) else None
    in
    run ~regression ~error ~title ~tags ~filename Dkcheck arguments

  let ok ?(regression = false) = run ~regression ~error:None

  let ko ~error = run ~regression:false ~error:(Some error)

  let export filename =
    let open Command in
    Process.run (fst (path Dkcheck)) (snd (path Dkcheck) ["-e"; filename])

  let check ~dep filename =
    let imported_paths =
      List.map (fun dep -> Import (Filename.dirname dep) |> mk_argument) dep
      |> List.concat
    in
    let open Command in
    let path, edit_arg = path Dkcheck in
    Process.spawn path (edit_arg (imported_paths @ [filename])) |> Process.check
end

module Meta = struct
  type argument =
    | No_meta
    | No_beta
    | Meta of string
    | Import of string
    | Quoting of [`Prod]
    | No_unquoting

  let mk_argument = function
    | No_meta -> ["--no-meta"]
    | No_beta -> ["--no-beta"]
    | Meta file -> ["-m"; file]
    | Import path -> ["-I"; path]
    | Quoting `Prod -> ["--quoting"; "prod"]
    | No_unquoting -> ["--no-unquoting"]

  let tag_of_argument = function
    | No_meta -> "no_meta"
    | No_beta -> "no_beta"
    | Meta _file -> "meta_file"
    | Import _path -> "import"
    | Quoting `Prod -> "quoting_prod"
    | No_unquoting -> "no_unquoting"

  let run ?(dep = []) ?(check_output = true) ~filename arguments =
    let tags = List.map tag_of_argument arguments in
    let arguments = List.map mk_argument arguments |> List.concat in
    let title =
      title ~action:"metaify" ~result:"succeeds" ~options:tags filename
    in
    let tags = "dkmeta" :: tags in
    let regression = Some (String.concat "_" (filename :: tags)) in
    let import_arguments =
      List.map (fun dir -> ["-I"; Filename.dirname dir]) dep |> List.concat
    in
    let preprocess () =
      (* Ensure we are not using old generated artifacts. *)
      let* () = remove_dkos () in
      Lwt_list.iter_s Check.export dep
    in
    let postprocess lines =
      if not check_output then return ()
      else
        let file = Temp.file (Filename.basename filename) in
        let oc = open_out file in
        let fmt = Format.formatter_of_out_channel oc in
        List.iter
          (fun line ->
            Log.info "%s" line;
            Format.fprintf fmt "%s@." line)
          lines;
        close_out oc;
        Check.check ~dep file
    in
    (* Add verbose logs from [dkmeta] if we are in debug mode. *)
    let log_dkmeta = if Cli.options.log_level = Cli.Debug then ["-v"] else [] in
    run ~regression ~error:None ~title ~tags ~filename Dkmeta
      (import_arguments @ log_dkmeta @ arguments)
      ~preprocess ~postprocess
end

module Pretty = struct
  type argument = |

  let mk_argument : argument -> _ = function _ -> .

  let tag_of_argument : argument -> _ = function _ -> .

  let run ?(dep = []) ~filename arguments =
    let tags = "beautify" :: List.map tag_of_argument arguments in
    let arguments = List.(map mk_argument arguments |> concat) in
    let title =
      title ~action:"pretty print" ~options:tags ~result:"succeeds" filename
    in
    let regression = Some (String.concat "_" (filename :: tags)) in
    let postprocess lines =
      let file = Temp.file ("pretty." ^ Filename.basename filename) in
      let oc = open_out file in
      let fmt = Format.formatter_of_out_channel oc in
      List.iter
        (fun line ->
          Log.info "%s" line;
          Format.fprintf fmt "%s@." line)
        lines;
      close_out oc;
      Check.check ~dep file
    in
    run ~regression ~error:None ~title ~tags ~filename Dkpretty arguments
      ~postprocess
end
