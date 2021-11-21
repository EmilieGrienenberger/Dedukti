module Check : sig
  type argument = Eta | Import of string

  (** [ok ?regression ~filename arguments] runs [dkcheck] on
     [filename] with [arguments].

      If [regression] is set to [true], the standard output of the
     test will be recorded into a file. This can be used to ensure the
     reduction strategy did not change for example.

     Any regression test is run in quiet mode and consequently
     [Cli.log_level] is ignored.

     If the [Cli.log_level] is:

     - [Report] (default), the test is run in quiet mode.

     - [Debug] (option "-v" (see {Tezt.Cli})), the test is run with
     argument "-d montru" (default value for verbose mode with
     [dkcheck]).

     - [Info] (option "-i" (see {Tezt.Cli})), the test is run with
     argument "-d n". Each top-level symbol is logged as well as the
     command run.*)
  val ok : ?regression:bool -> filename:string -> argument list -> unit

  (** [ko error ~filename arguments] is similar to [ok] but a failure
     is expected when running [dkcheck]. It is checked that the error
     returned by [dkcheck] is [error]. *)
  val ko :
    error:[`Code of int | `System] -> filename:string -> argument list -> unit
end

module Meta : sig
  type argument = No_meta | No_beta | Meta of string | Import of string

  (** [run ?dep ~filename arguments] runs [dkmeta] on [filename] with
     [arguments].

      [dep] should contain files which are required for executing the
     command. Either because the module is a dependency of [filename],
     or because it is a dependency of a file given with the option
     [Meta]. For every file in [dep], their directory is imported
     using the option [Import]. *)

  val run : ?dep:string list -> filename:string -> argument list -> unit
end
