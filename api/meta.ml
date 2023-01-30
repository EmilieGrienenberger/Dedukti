open Kernel
open Parsers

module type ENCODING = sig
  val md : Basic.mident

  val entries : string list -> Entry.entry list

  val safe : bool

  val signature : string list -> Signature.t

  val encode_term :
    ?sg:Signature.t -> ?ctx:Term.typed_context -> Term.term -> Term.term

  val decode_term : Term.term -> Term.term

  val encode_rule : ?sg:Signature.t -> 'a Rule.rule -> 'a Rule.rule
end

module NO_ENCODING = struct
  open Basic
  open Term

  let md = mk_mident "no_encoding"

  let entries additional_decls =
    let mk_decl id =
      Entry.Decl
        ( dloc,
          mk_ident id,
          Signature.Public,
          Signature.Definable Free,
          mk_Type dloc )
    in
    List.map mk_decl additional_decls

    let signature additional_decls =
    let find_object_file = Files.find_object_file_exn Files.empty in
    let sg = Signature.make ~explicit_import:false md find_object_file in
    let mk_decl id =
      Signature.add_declaration sg dloc (mk_ident id) Signature.Public
        (Signature.Definable Free) (mk_Type dloc)
    in
    List.iter mk_decl additional_decls;
    sg

  let safe = false

  let encode_term ?sg:_ ?ctx:_ t = t

  let encode_rule ?sg:_ r = r

  let decode_term t = t
end

module type ENCODING_ENTRIES = sig
  include ENCODING
  val additional_decls : string list
  val encode_entry :
    ?sg:Signature.t -> ?ctx:Term.typed_context -> Entry.entry -> Term.term list

  val decode_entry : Term.term -> Entry.entry option
end

exception Not_a_pattern

let rec pattern_of_term t =
  let open Term in
  match t with
  | Kind | Type _ | Pi _ -> raise Not_a_pattern
  | Lam (lc, x, _, te) -> Rule.Lambda (lc, x, pattern_of_term te)
  | App (Const (lc, name), a, args) ->
      Rule.Pattern (lc, name, List.map pattern_of_term (a :: args))
  | App (DB (lc, x, n), a, args) ->
      Rule.Var (lc, x, n, List.map pattern_of_term (a :: args))
  | Const (lc, name) -> Rule.Pattern (lc, name, [])
  | DB (lc, x, n) -> Rule.Var (lc, x, n, [])
  | _ -> raise Not_a_pattern

module MakeEntries (E : ENCODING) : ENCODING_ENTRIES = struct
  include E
  open Basic
  open Term

  let name_of str = mk_name E.md (mk_ident str)
  let const_of str = mk_Const dloc (name_of str)

  let additional_decls = ["Decl"; "Def"; "Rule"; "Public"; "Private"; "Static"; "Definable"; "Injective"; "EmptyEntry" ; "Opaque"; "Transparent"]

  let encode_id id = const_of (string_of_ident id)

  let encode_rules rules =
    List.map
      (fun rule ->
        let open Rule in
        let {name=_; ctx=_ ; pat = p; rhs =r} = encode_rule rule in
        mk_App2 (const_of "Rule") [pattern_to_term p ; encode_term r])
      rules

  let encode_scope scope =
    match scope with
    | Signature.Public  -> const_of "Public"
    | Signature.Private -> const_of "Private"

  let encode_opacity opaque =
    if opaque then const_of "Opaque" else const_of "Transparent"

  let encode_staticity staticity =
    match staticity with
    | Signature.Static      -> const_of "Static"
    | Signature.Definable _ -> const_of "Definable"
    | Signature.Injective   -> const_of "Injective"

  let encode_decl id scope staticity ty =
    mk_App2 (const_of "Decl") [encode_id id ; encode_scope scope ; encode_staticity staticity ; encode_term ty]

  let encode_def id scope op ty te =
    match ty with
    | None    ->
        mk_App2 (const_of "Def") [encode_id id ; encode_scope scope ; encode_opacity op ; encode_term te]
    | Some t  ->
        mk_App2 (const_of "Def") [encode_id id ; encode_scope scope ; encode_opacity op ; encode_term t ; encode_term te]

  let encode_entry ?sg:_ ?ctx:_ e =
    match e with
    | Entry.Decl(_, id, scope, staticity, ty) -> [encode_decl id scope staticity ty]
    | Entry.Def(_, id, scope, op, ty, te) -> [encode_def id scope op ty te]
    | Entry.Rules(_, rules) -> encode_rules rules
    | _ -> failwith("All entries should be declarations, definitions, or rewrite rules when reifying entries.")

  let decode_id = function
    | Const(_,name) -> id name
    | _ -> assert false

  let decode_scope = function
    | Const(_,name) when name_eq name (name_of "Public") -> Signature.Public
    | Const(_,name) when name_eq name (name_of "Private") -> Signature.Private
    | _ -> assert false

  let decode_staticity = function
    | Const(_,name) when name_eq name (name_of "Static") -> Signature.Static
    | Const(_,name) when name_eq name (name_of "Definable") -> Signature.Definable(Term.Free)
    | Const(_,name) when name_eq name (name_of "Injective") -> Signature.Injective
    | _ -> assert false

  let decode_opacity = function
    | Const(_,name) when name_eq name (name_of "Opaque") -> true
    | Const(_,name) when name_eq name (name_of "Transparent") -> false
    | _ -> assert false

  let decode_Decl a = function
    | [encoded_scope ; encoded_staticity; encoded_ty] ->
        Entry.Decl(dloc, decode_id a, decode_scope encoded_scope, decode_staticity encoded_staticity, decode_term encoded_ty)
    | _ -> assert false

  let decode_Def a = function
    | [encoded_scope ; encoded_opacity ; encoded_term] ->
        Entry.Def(dloc, decode_id a, decode_scope encoded_scope, decode_opacity encoded_opacity, None, decode_term encoded_term)
    | [encoded_scope ; encoded_opacity ; encoded_type ; encoded_term ] ->
        Entry.Def(dloc, decode_id a, decode_scope encoded_scope, decode_opacity encoded_opacity, Some(decode_term encoded_type), decode_term encoded_term)
    | _ -> assert false

  module VarSet = Set.Make(struct
                      type t = ident
                      let compare a b = if (ident_eq a b) then 1 else 0
                    end)

  let rec free_vars_of_pattern pat_list =
    let open Rule in
    let fv_pat_tl = free_vars_of_pattern (List.tl pat_list) in
    let union_fv_pat_tl = VarSet.union fv_pat_tl in
    match (List.hd pat_list) with
    | Var(_,id,_ ,var_pat_list) ->
        let fv_var_pat_list = free_vars_of_pattern var_pat_list in
          VarSet.add id (union_fv_pat_tl fv_var_pat_list)
    | Pattern(_,_,pat_pat_list) -> union_fv_pat_tl (free_vars_of_pattern pat_pat_list)
    | Lambda(_,id,pat) ->
        let fv_abs_pat = VarSet.remove id (free_vars_of_pattern [pat]) in
        union_fv_pat_tl fv_abs_pat
    | _ -> failwith("Brackets are not yet managed for meta-entries")

  let decode_Rule encoded_pat = function
    | [encoded_rhs] ->
        let open Rule in
        let pat = pattern_of_term (decode_term encoded_pat) in
        let ctx = List.map (fun id -> (dloc, id, None)) (VarSet.elements(free_vars_of_pattern [pat])) in
        let rhs = decode_term encoded_rhs in
        let ptr = {name = Beta; ctx = ctx; pat = pat; rhs = rhs} in
        Entry.Rules(dloc, [ptr])
    | _ -> assert false

  let decode_entry = function
    | Const(_, name) when name_eq name (name_of "EmptyEntry") -> None
    | App(f, a, args) ->
        (match f with
         | Const(_, name) when name_eq name (name_of "Decl")  -> Some(decode_Decl a args)
         | Const(_, name) when name_eq name (name_of "Def")   -> Some(decode_Def a args)
         | Const(_, name) when name_eq name (name_of "Rule")  -> Some(decode_Rule a args)
         | _                                                  -> assert false)
    | _               -> assert false
end

module RNS = Set.Make (struct
  type t = Rule.rule_name

  let compare = compare
end)

type cfg = {
  meta_signature : Signature.t;
  (* Signature containing meta rules *)
  mutable meta_rules : RNS.t option;
  (* Set of meta_rules used to normalize *)
  beta : bool;
  (* Allows beta doing normalization *)
  register_before : bool;
  (* entries are registered before they have been normalized *)
  encoding : (module ENCODING);
  (* Encoding specify a quoting mechanism *)
  metaentries : bool;
  (* Entries are reified *)
  decoding : bool; (* If false, the term is not decoded after normalization *)
}

let rule_name (Rule.{name; _} : Rule.partially_typed_rule) = name

let signature_add_rule sg r = Signature.add_rules sg [Rule.to_rule_infos r]

(* Several rules might be bound to different constants *)
let signature_add_rules sg rs = List.iter (signature_add_rule sg) rs

let default_config ?meta_rules ?(beta = true) ?(encoding = (module NO_ENCODING : ENCODING))
      ?(metaentries=false) ?(decoding = true) ?(register_before = true) ~load_path () =
  let meta_mident = Basic.mk_mident "<meta>" in
  let find_object_file = Files.find_object_file_exn load_path in
  let meta_signature =
    Signature.make ~explicit_import:false meta_mident find_object_file
  in
  let module E = (val encoding) in
  let module Entries = (val (module MakeEntries(E) : ENCODING_ENTRIES)) in
  let additional_decls = Entries.additional_decls in
  Signature.import_signature meta_signature (E.signature additional_decls);
  (* FIXME: only one traversal is needed instead of 2 *)
  let meta_rules =
    Option.map
      (fun rules ->
        signature_add_rules meta_signature rules;
        RNS.of_list (List.map rule_name rules))
      meta_rules
  in
  {meta_signature; meta_rules; beta; encoding; metaentries; decoding; register_before}

let add_rules cfg rules =
  signature_add_rules cfg.meta_signature rules;
  let rules = RNS.of_list (List.map rule_name rules) in
  match cfg.meta_rules with
  | None -> cfg.meta_rules <- Some rules
  | Some previous_rules ->
      cfg.meta_rules <- Some (RNS.union rules previous_rules)

(* This is a shortcut so that if a symbol is not found in the signature, we can still reduce. *)
let unsafe_finder sg l name =
  (* FIXME: pattern match properly on the error. *)
  try Kernel.Signature.get_dtree sg l name with _ -> Dtree.empty

(* A dkmeta configuration to a reduction configuration *)
let red_cfg : cfg -> Reduction.red_cfg =
 fun cfg ->
  let open Reduction in
  let red_cfg =
    {
      default_cfg with
      beta = cfg.beta;
      target = Snf;
      finder = unsafe_finder;
      strat = ByValue;
    }
  in
  match cfg.meta_rules with
  | None -> {red_cfg with select = Some (fun _ -> true)}
  | Some meta_rules ->
      {red_cfg with select = Some (fun r -> RNS.mem r meta_rules)}

module PROD = struct
  open Basic
  open Term

  let md = mk_mident "prod"

  let entries additional_decls =
    let mk_decl id =
      Entry.Decl
        ( dloc,
          mk_ident id,
          Signature.Public,
          Signature.Definable Free,
          mk_Type dloc )
    in
    List.map mk_decl (["ty"; "prod"] @ additional_decls)

  let signature additional_decls =
    let find_object_file = Files.find_object_file_exn Files.empty in
    let sg = Signature.make ~explicit_import:false md find_object_file in
    let mk_decl id =
      Signature.add_declaration sg dloc (mk_ident id) Signature.Public
        (Signature.Definable Free) (mk_Type dloc)
    in
    List.iter mk_decl (["ty"; "prod"] @ additional_decls);
    sg

  let safe = false

  let name_of str = mk_name md (mk_ident str)

  let const_of str = mk_Const dloc (name_of str)

  let rec encode_term t =
    match t with
    | Kind -> assert false
    | Type lc -> encode_type lc
    | DB (lc, x, n) -> encode_DB lc x n
    | Const (lc, name) -> encode_Const lc name
    | Lam (lc, x, mty, te) -> encode_Lam lc x mty te
    | App (f, a, args) -> encode_App f a args
    | Pi (lc, x, a, b) -> encode_Pi lc x a b

  and encode_type lc = mk_Const lc (name_of "ty")

  and encode_DB lc x n = mk_DB lc x n

  and encode_Const _ name = mk_Const dloc name

  and encode_Lam _ x mty te =
    let mty' =
      match mty with None -> None | Some ty -> Some (encode_term ty)
    in
    mk_Lam dloc x mty' (encode_term te)

  and encode_App f a args =
    mk_App2 (encode_term f) (List.map encode_term (a :: args))

  and encode_Pi _ x a b =
    mk_App (const_of "prod") (encode_term a)
      [mk_Lam dloc x (Some (encode_term a)) (encode_term b)]

  (* Using typed context here does not make sense *)
  let encode_pattern pattern : Rule.pattern = pattern

  let encode_rule (r : 'a Rule.rule) =
    let open Rule in
    {r with pat = encode_pattern r.pat; rhs = encode_term r.rhs}

  let encode_term ?sg:_ ?ctx:_ t = encode_term t

  let encode_rule ?sg:_ r = encode_rule r

  let rec decode_term t =
    match t with
    | Kind -> assert false
    | Pi _ -> assert false
    | App (f, a, args) -> decode_App f a args
    | Lam (lc, x, mty, te) -> decode_Lam lc x mty te
    | Const (lc, name) -> decode_Const lc name
    | Type _ | DB _ -> t

  and decode_Const lc name =
    if name_eq name (name_of "ty") then mk_Type lc else mk_Const lc name

  and decode_Lam lc x mty te =
    let mty' =
      match mty with None -> None | Some mty -> Some (decode_term mty)
    in
    mk_Lam lc x mty' (decode_term te)

  and decode_App f a args =
    match f with
    | Const (_, name) ->
        if name_eq name (name_of "prod") then
          match args with
          | [Lam (_, x, Some a, b)] ->
              mk_Pi dloc x (decode_term a) (decode_term b)
          | _ -> assert false
        else mk_App (decode_term f) (decode_term a) (List.map decode_term args)
    | _ -> mk_App (decode_term f) (decode_term a) (List.map decode_term args)
end

module LF = struct
  open Basic
  open Term

  let md = mk_mident "lf"

  let entries additional_decls =
    let mk_decl id =
      Entry.Decl
        ( dloc,
          mk_ident id,
          Signature.Public,
          Signature.Definable Free,
          mk_Type dloc )
    in
    List.map mk_decl (["ty"; "var"; "sym"; "lam"; "app"; "prod"] @ additional_decls)

  let signature additional_decls =
    let find_object_file = Files.find_object_file_exn Files.empty in
    let sg = Signature.make ~explicit_import:false md find_object_file in
    let mk_decl id =
      Signature.add_declaration sg dloc (mk_ident id) Signature.Public
        (Signature.Definable Free) (mk_Type dloc)
    in
    List.iter mk_decl (["ty"; "var"; "sym"; "lam"; "app"; "prod"] @ additional_decls);
    sg

  let safe = false

  let name_of str = mk_name md (mk_ident str)

  let const_of str = mk_Const dloc (name_of str)

  let rec encode_term t =
    match t with
    | Kind -> assert false
    | Type lc -> encode_type lc
    | DB (lc, x, n) -> encode_DB lc x n
    | Const (lc, name) -> encode_Const lc name
    | Lam (lc, x, mty, te) -> encode_Lam lc x mty te
    | App (f, a, args) -> encode_App f a args
    | Pi (lc, x, a, b) -> encode_Pi lc x a b

  and encode_type _ = const_of "ty"

  and encode_DB lc x n = mk_App (const_of "var") (mk_DB lc x n) []

  and encode_Const _ name = mk_App (const_of "sym") (mk_Const dloc name) []

  and encode_Lam _ x mty te =
    let mty' =
      match mty with None -> None | Some ty -> Some (encode_term ty)
    in
    mk_App (const_of "lam") (mk_Lam dloc x mty' (encode_term te)) []

  and encode_App f a args =
    let rec encode_app2 a args =
      match (a, args) with
      | _, [] -> assert false
      | a, [x] -> mk_App (const_of "app") a [encode_term x]
      | a, x :: l -> encode_app2 (mk_App (const_of "app") a [encode_term x]) l
    in
    encode_app2 (encode_term f) (a :: args)

  and encode_Pi _ x a b =
    mk_App (const_of "prod") (encode_term a)
      [mk_Lam dloc x None (encode_term b)]

  (* Using typed context here does not make sense *)
  let rec encode_pattern pattern : Rule.pattern =
    let open Rule in
    match pattern with
    | Var (lc, id, n, ps) -> Var (lc, id, n, List.map encode_pattern ps)
    | Brackets term -> Brackets (encode_term term)
    | Lambda (lc, id, p) ->
        Pattern (lc, name_of "lam", [Lambda (lc, id, encode_pattern p)])
    | Pattern (lc, n, []) -> Pattern (lc, name_of "sym", [Pattern (lc, n, [])])
    | Pattern (lc, n, ps) ->
        Pattern
          ( lc,
            name_of "app",
            Pattern (lc, name_of "sym", [Pattern (lc, n, [])])
            :: List.map encode_pattern ps )

  let encode_rule (r : 'a Rule.rule) =
    let open Rule in
    {r with pat = encode_pattern r.pat; rhs = encode_term r.rhs}

  let encode_term ?sg:_ ?ctx:_ t = encode_term t

  let encode_rule ?sg:_ r = encode_rule r

  let rec decode_term t =
    match t with
    | Kind -> assert false
    | Type _ -> assert false
    | DB (lc, x, n) -> decode_DB lc x n
    | Const (lc, name) -> decode_Const lc name
    | Lam (lc, x, mty, te) -> decode_Lam lc x mty te
    | App (f, a, args) -> decode_App f a args
    | Pi (lc, x, a, b) -> decode_Pi lc x a b

  and decode_DB lc x n = mk_DB lc x n

  and decode_Const lc name =
    if name_eq name (name_of "ty") then mk_Type dloc else mk_Const lc name

  and decode_Lam lc x mty te =
    let mty' =
      match mty with None -> None | Some mty -> Some (decode_term mty)
    in
    mk_Lam lc x mty' (decode_term te)

  and decode_App f a args =
    match f with
    | Const (_, name) ->
        if name_eq name (name_of "prod") then
          match (a, args) with
          | a, [Lam (_, x, None, b)] ->
              mk_Pi dloc x (decode_term a) (decode_term b)
          | _ -> assert false
        else if name_eq name (name_of "sym") then decode_term a
        else if name_eq name (name_of "var") then decode_term a
        else if name_eq name (name_of "app") then
          mk_App2 (decode_term a) (List.map decode_term args)
        else if name_eq name (name_of "lam") then decode_term a
        else mk_App (decode_term f) (decode_term a) (List.map decode_term args)
    | _ ->
        decode_App (decode_term f) (decode_term a) (List.map decode_term args)

  and decode_Pi _ _ _ _ = assert false
end

module APP = struct
  open Basic
  open Term

  let md = mk_mident "ltyped"

  let entries additional_decls =
    let mk_decl id =
      Entry.Decl
        ( dloc,
          mk_ident id,
          Signature.Public,
          Signature.Definable Free,
          mk_Type dloc )
    in
    List.map mk_decl (["ty"; "var"; "sym"; "lam"; "app"; "prod"] @ additional_decls)

  let signature additional_decls =
    let find_object_file = Files.find_object_file_exn Files.empty in
    let sg = Signature.make ~explicit_import:false md find_object_file in
    let mk_decl id =
      Signature.add_declaration sg dloc (mk_ident id) Signature.Public
        (Signature.Definable Free) (mk_Type dloc)
    in
    List.iter mk_decl (["ty"; "var"; "sym"; "lam"; "app"; "prod"] @ additional_decls);
    sg

  let safe = true

  let name_of str = mk_name md (mk_ident str)

  let const_of str = mk_Const dloc (name_of str)

  let rec encode_term sg ctx t =
    match t with
    | Kind -> assert false
    | Type lc -> encode_type sg ctx lc
    | DB (lc, x, n) -> encode_DB sg ctx lc x n
    | Const (lc, name) -> encode_Const sg ctx lc name
    | Lam (lc, x, Some ty, te) -> encode_Lam sg ctx lc x ty te
    | Lam _ -> assert false
    | App (f, a, args) -> encode_App sg ctx f a args
    | Pi (lc, x, a, b) -> encode_Pi sg ctx lc x a b

  and encode_type _ _ _ = const_of "ty"

  and encode_DB _ _ lc x n = mk_App (const_of "var") (mk_DB lc x n) []

  and encode_Const _ _ _ name = mk_App (const_of "sym") (mk_Const dloc name) []

  and encode_Lam sg ctx lc x ty te =
    let ctx' = (lc, x, ty) :: ctx in
    let tyf = Typing.Default.infer sg ctx (mk_Lam lc x (Some ty) te) in
    let tyf' = PROD.encode_term tyf in
    mk_App (const_of "lam") tyf'
      [mk_Lam dloc x (Some (encode_term sg ctx ty)) (encode_term sg ctx' te)]

  and encode_App sg ctx f a args = encode_app2 sg ctx f (a :: args)

  and encode_app2 sg ctx f args =
    let aux f f' a =
      let tyf = Typing.Default.infer sg ctx f in
      let tyf' = PROD.encode_term tyf in
      ( Term.mk_App2 f [a],
        mk_App (const_of "app") tyf' [f'; encode_term sg ctx a] )
    in
    snd
    @@ List.fold_left
         (fun (f, f') a -> aux f f' a)
         (f, encode_term sg ctx f)
         args

  and encode_Pi sg ctx lc x a b =
    let ctx' = (lc, x, a) :: ctx in
    mk_App (const_of "prod")
      (mk_Lam dloc x (Some (encode_term sg ctx a)) (encode_term sg ctx' b))
      []

  let rec encode_pattern sg ctx pattern =
    let open Rule in
    let dummy = Var (Basic.dloc, mk_ident "_", 0, []) in
    let mk_pat_app l r =
      Pattern (Basic.dloc, name_of "app", [dummy; l; encode_pattern sg ctx r])
    in
    match pattern with
    | Var (lc, id, n, ps) -> Var (lc, id, n, List.map (encode_pattern sg ctx) ps)
    | Brackets term -> Brackets (encode_term sg ctx term)
    | Lambda (lc, id, p) ->
        Pattern
          (lc, name_of "lam", [dummy; Lambda (lc, id, encode_pattern sg ctx p)])
    | Pattern (lc, n, []) -> Pattern (lc, name_of "sym", [Pattern (lc, n, [])])
    | Pattern (lc, n, [a]) ->
        Pattern
          ( lc,
            name_of "app",
            [
              dummy;
              Pattern (lc, name_of "sym", [Pattern (lc, n, [])]);
              encode_pattern sg ctx a;
            ] )
    | Pattern (lc, n, a :: l) ->
        List.fold_left
          (fun p arg -> mk_pat_app p arg)
          (encode_pattern sg ctx (Pattern (lc, n, [])))
          (a :: l)

  let encode_rule sg r =
    let r' = Rule.untyped_rule_of_rule_infos (Rule.to_rule_infos r) in
    let _, r'' = Typing.Default.check_rule sg r' in
    let open Rule in
    {
      r with
      pat = encode_pattern sg r''.ctx r.pat;
      rhs = encode_term sg r''.ctx r.rhs;
    }

  let fake_sig () =
    let find_object_file = Files.find_object_file_exn Files.empty in
    Signature.make ~explicit_import:false (Basic.mk_mident "") find_object_file

  let encode_term ?(sg = fake_sig ()) ?(ctx = []) t = encode_term sg ctx t

  let encode_rule ?(sg = fake_sig ()) r = encode_rule sg r

  let rec decode_term t =
    match t with
    | Kind -> assert false
    | Type _ -> assert false
    | DB (lc, x, n) -> decode_DB lc x n
    | Const (lc, name) -> decode_Const lc name
    | Lam (lc, x, mty, te) -> decode_Lam lc x mty te
    | App (f, a, args) -> decode_App f a args
    | Pi (lc, x, a, b) -> decode_Pi lc x a b

  and decode_DB lc x n = mk_DB lc x n

  and decode_Const lc name =
    if name_eq name (name_of "ty") then mk_Type dloc else mk_Const lc name

  and decode_Lam lc x mty te =
    let mty' =
      match mty with None -> None | Some mty -> Some (decode_term mty)
    in
    mk_Lam lc x mty' (decode_term te)

  and decode_App f a args =
    match f with
    | Const (_, name) ->
        if name_eq name (name_of "prod") then
          match a with
          | Lam (_, x, Some a, b) ->
              mk_Pi dloc x (decode_term a) (decode_term b)
          | _ -> assert false
        else if name_eq name (name_of "sym") then decode_term a
        else if name_eq name (name_of "var") then decode_term a
        else if name_eq name (name_of "app") then
          match args with
          | [f; a] -> Term.mk_App2 (decode_term f) [decode_term a]
          | _ -> assert false
        else if name_eq name (name_of "lam") then
          match args with [a] -> decode_term a | _ -> assert false
        else mk_App (decode_term f) (decode_term a) (List.map decode_term args)
    | _ -> mk_App (decode_term f) (decode_term a) (List.map decode_term args)

  and decode_Pi _ _ _ _ = assert false
end

let encode_terms cfg env term =
  let module E = (val cfg.encoding) in
  if E.safe then
    match env with
    | None ->
        Errors.fail_sys_error
          ~msg:
          "A type checking environment must be provided when a safe \
           encoding is used."
          ()
    | Some env ->
        let sg = Env.get_signature env in
        E.encode_term ~sg term
  else E.encode_term term

let encode_entries cfg env entry =
  let module E = (val cfg.encoding) in
  let module Entry = (val (module MakeEntries(E) : ENCODING_ENTRIES)) in
  if E.safe then
    match env with
    | None ->
        Errors.fail_sys_error
          ~msg:
          "A type checking environment must be provided when a safe \
           encoding is used."
          ()
    | Some env ->
        let sg = Env.get_signature env in
        Entry.encode_entry ~sg entry
  else Entry.encode_entry entry

let decode_terms cfg term =
  let module E = (val cfg.encoding) in
  E.decode_term term

let decode_entries cfg entry =
  let module E = (val cfg.encoding) in
  let module Entry = (val (module MakeEntries(E) : ENCODING_ENTRIES)) in
  Entry.decode_entry entry

let normalize cfg sg term =
  let red = red_cfg cfg in
  Reduction.Default.reduction red sg term

(* [cfg.meta_rules = None] means we use the type checking environment
       for normalisation. *)
let get_meta_signature cfg env =
  match cfg.meta_rules with
  | Some _ -> cfg.meta_signature
  | None -> (
      match env with
      | None ->
          Errors.fail_sys_error
            ~msg:
              "A type checking environment must be provided when the \
               normalisation strategy is done via the type checking \
               environment"
            ()
      | Some env -> Env.get_signature env)

let process_term ?env cfg term =
  let term' = encode_terms cfg env term in
  let sg = get_meta_signature cfg env in
  let term'' = normalize cfg sg term' in
  if cfg.decoding then decode_terms cfg term'' else term''

let process_rule env cfg (r : Rule.partially_typed_rule) =
  let open Rule in
  let meta_signature = get_meta_signature cfg (Some env) in
  let module E = (val cfg.encoding) in
  let sg = Env.get_signature env in
  let r' = E.encode_rule ~sg r in
  let pat' = normalize cfg meta_signature (Rule.pattern_to_term r'.pat) in
  let pat'' =
    if cfg.decoding then pattern_of_term (E.decode_term pat')
    else pattern_of_term pat'
  in
  let rhs' = normalize cfg meta_signature r'.rhs in
  let rhs'' = if cfg.decoding then decode_terms cfg rhs' else rhs' in
  {pat = pat''; rhs = rhs''; ctx = r.ctx; name = r.name}

module D = Basic.Debug

let debug_flag = D.register_flag "Dkmeta"

let bmag fmt = "\027[90m" ^^ fmt ^^ "\027[0m%!"

let log fmt = D.debug debug_flag (bmag fmt)

let process_meta_entry cfg env entry =
  let open Entry in
  let module E = (val cfg.encoding) in
  let module Entries = (val (module MakeEntries(E) : ENCODING_ENTRIES)) in
  let term' = encode_entries cfg env entry in
  let sg = get_meta_signature cfg env in
  let term'' = List.map (normalize cfg sg) term' in
  if cfg.decoding then List.filter_map (decode_entries cfg) term''
  else
    List.map
      (fun term -> Decl(Basic.dloc, Basic.dmark, Signature.Public, Signature.Static, term))
      term''

let process_entry cfg env entry =
  let open Entry in
  let open Rule in
  let sg = Env.get_signature env in
  let md = Env.get_name env in
  let module E = (val cfg.encoding) in
  let module Entries = (val (module MakeEntries(E) : ENCODING_ENTRIES)) in
  match entry with
  | Decl (lc, id, sc, st, ty) ->
      log "[NORMALIZE] %a" Basic.pp_ident id;
      let ty' = process_term ~env cfg ty in
      if cfg.register_before then Signature.add_declaration sg lc id sc st ty
      else Signature.add_declaration sg lc id sc st ty';
      Decl (lc, id, sc, st, ty')
  | Def (lc, id, sc, opaque, ty, te) -> (
      log "[NORMALIZE] %a" Basic.pp_ident id;
      let cst = Basic.mk_name md id in
      let rule =
        {name = Delta cst; ctx = []; pat = Pattern (lc, cst, []); rhs = te}
      in
      let safe_ty =
        match ty with
        | None when E.safe -> Env.infer env te
        | Some ty -> ty
        | _ -> Term.mk_Type Basic.dloc
      in
      let safe_ty' = process_term ~env cfg safe_ty in
      let te' = process_term ~env cfg te in
      (if cfg.register_before then
       let _ =
         Signature.add_declaration sg lc id sc (Signature.Definable Free)
           safe_ty
       in
       Signature.add_rules sg
         (List.map Rule.to_rule_infos [{rule with rhs = te}])
      else
        let _ =
          Signature.add_declaration sg lc id sc (Signature.Definable Free)
            safe_ty'
        in
        Signature.add_rules sg
          (List.map Rule.to_rule_infos [{rule with rhs = te'}]));
      match ty with
      | None -> Def (lc, id, sc, opaque, None, te')
      | Some _ -> Def (lc, id, sc, opaque, Some safe_ty', te'))
  | Rules (lc, rs) ->
      (* Signature.add_rules !sg (List.map Rule.to_rule_infos rs); *)
      let rs' = List.map (process_rule env cfg) rs in
      if cfg.register_before then
        Signature.add_rules sg (List.map Rule.to_rule_infos rs)
      else Signature.add_rules sg (List.map Rule.to_rule_infos rs');
      Rules (lc, rs')
  | _ -> entry

module MetaConfiguration :
  Processor.S with type t = Rule.partially_typed_rule list = struct
  type t = Rule.partially_typed_rule list

  let rules = ref []

  let handle_entry _ = function
    | Entry.Rules (_, rs) -> rules := rs :: !rules
    (* TODO: Handle definitions *)
    | _ -> ()

  let get_data _ =
    let rs = List.flatten !rules in
    rules := [];
    rs
end

type _ Processor.t += MetaRules : Rule.partially_typed_rule list Processor.t

let _ =
  let equal (type a b) :
      a Processor.t * b Processor.t ->
      (a Processor.t, b Processor.t) Processor.Registration.equal option =
    function
    | MetaRules, MetaRules -> Some (Processor.Registration.Refl MetaRules)
    | _ -> None
  in
  Processor.Registration.register_processor MetaRules {equal}
    (module MetaConfiguration)

let parse_meta_files files =
  (* Load path is not needed since no importation is done via the
     [MetaRules] processor. *)
  let load_path = Files.empty in
  Processor.fold_files ~load_path ~files
    ~f:(fun rules acc -> rules :: acc)
    ~default:[] MetaRules
  |> List.concat

let make_meta_processor cfg ~post_processing =
  let module Meta = struct
    type t = unit

    let handle_entry env entry =
      if cfg.metaentries then List.iter (post_processing env) (process_meta_entry cfg (Some env) entry)
      else post_processing env (process_entry cfg env entry)

    let get_data _ = ()
  end in
  (module Meta : Processor.S with type t = unit)
