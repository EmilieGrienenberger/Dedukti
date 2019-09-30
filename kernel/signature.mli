(** Global Environment *)

open Basic
open Term
open Rule

type Debug.flag += D_module

type file = string

type signature_error =
  | UnmarshalBadVersionNumber of loc * file
  | UnmarshalSysError     of loc * file * string
  | UnmarshalUnknown      of loc * file
  | SymbolNotFound        of loc * name
  | AlreadyDefinedSymbol  of loc * name
  | CannotMakeRuleInfos   of Rule.rule_error
  | CannotBuildDtree      of Dtree.dtree_error
  | CannotAddRewriteRules of loc * name
  | ConfluenceErrorImport of loc * mident * Confluence.confluence_error
  | ConfluenceErrorRules  of loc * rule_infos list * Confluence.confluence_error
  | GuardNotSatisfied     of loc * term * term
  | CannotExportModule    of mident * exn

exception Signature_error of signature_error

type staticity = Static | Definable

type t

val make                : mident -> (loc -> mident -> file) -> t
(** [make file] creates a new signature corresponding to the file [file]. *)

val get_name            : t -> mident
(** [get_name sg] returns the name of the signature [sg]. *)

val export              : t -> out_channel -> unit
(** [export sg oc] saves the current environment in [oc] file.*)

val import              : t -> loc -> mident -> unit
(** [import sg md] impots the module [md] in the signature [sg]. *)

val import_signature    : t -> t -> unit
(** [import sg sg_ext] imports the signature [sg_ext] into the signature [sg]. *)

val is_static           : t -> loc -> name -> bool
(** [is_injective sg l cst] is true when [cst] is a static symbol. *)

val get_type            : t -> loc -> name -> term
(** [get_type sg l md id] returns the type of the constant [md.id] inside the
    environement [sg]. *)

val get_dtree           : t -> loc -> name -> Dtree.t
(** [get_dtree sg filter l cst] returns the decision/matching tree associated
    with [cst] inside the environment [sg]. *)

val get_rules           : t -> loc -> name -> rule_infos list
(** [get_rules sg lc cst] returns a list of rules that defines the symbol. *)

val add_external_declaration     : t -> loc -> name -> staticity -> term -> unit
(** [add_external_declaration sg l cst st ty] declares the symbol [id] of type
    [ty] and staticity [st] in the environment [sg]. *)

val add_declaration     : t -> loc -> ident -> staticity -> term -> unit
(** [add_declaration sg l id st ty] declares the symbol [id] of type [ty]
    and staticity [st] in the environment [sg]. *)

val add_rules           : t -> Rule.rule_infos list -> unit
(** [add_rules sg rule_lst] adds a list of rule to a symbol in the environement [sg].
    All rules must be on the same symbol. *)

val fail_on_symbol_not_found : bool ref
(** if [false], does 2 things:
    1. [get_dtree] won't fail if the symbol has not be found
    2. [add_rules] won't fail if a rule is added on a symbol not present
       in the signature. However, a fresh symbol is added.
    This flag is intented to facilitate the use of the module Reduction
    when it is used without the module Typing such as in dkmeta. *)

type rw_infos =
  {
    stat          : staticity;
    ty            : term;
    rules         : rule_infos list;
    decision_tree : Dtree.t option
  }

val fold_symbols : (mident -> ident -> rw_infos -> 'a -> 'a) -> t -> 'a -> 'a
(** [fold_symbols f sg t] folds the function [f] on all symbol_infos in the signature
    starting from [t]. *)

val iter_symbols : (mident -> ident -> rw_infos -> unit) -> t -> unit
(** [iter_symbols f sg] iters the function [f] on all symbol_infos in the signature. *)
