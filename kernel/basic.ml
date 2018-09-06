(** Basic Datatypes *)


(** {2 Identifiers (hashconsed strings)} *)

type ident = string

let string_of_ident s = s

let ident_eq s1 s2 = s1==s2 || s1=s2


type mident = string

let string_of_mident s = s

let mident_eq = ident_eq


(* TODO: rename ident *)
type name = mident * ident

let mk_name md id = (md,id)

let name_eq (m,s) (m',s') = mident_eq m m' && ident_eq s s'

let md = fst
let id = snd



module WS = Weak.Make(
struct
  type t        = ident
  let equal     = ident_eq
  let hash      = Hashtbl.hash
end )

let shash        = WS.create 251

let mk_ident     = WS.merge shash

let mk_mident md =
  let base = Filename.basename md in
  try Filename.chop_extension base with _ -> base

let dmark       = mk_ident "$"

(** {2 Lists with Length} *)

module LList = struct
  type 'a t= {
    len : int;
    lst : 'a list;
  }

  let cons x {len;lst} = {len=len+1; lst=x::lst}
  let nil = {len=0;lst=[];}

  let make ~len lst =
    assert (List.length lst = len);
    {lst;len}

  let make_unsafe ~len lst = {len;lst}
  (** make_unsafe [n] [l] is as make [n] [l] without checking that the length of [l] is [n] *)

  let of_list  lst = {len=List.length lst ; lst}
  let of_array arr = {len=Array.length arr; lst=Array.to_list arr}

  let len x = x.len
  let lst x = x.lst
  let is_empty x = x.len = 0

  let map f {len;lst} = {len; lst=List.map f lst}
  let append_l {len;lst} l = {len=len+List.length l; lst=lst@l}

  let nth l i = assert (i<l.len); List.nth l.lst i

  let remove i {len;lst} =
    let rec aux c lst = match lst with
      | []        -> assert false
      | x::lst'   -> if c==0 then lst' else x::(aux (c-1) lst')
    in
    {len=len-1; lst=aux i lst}
end

(** {2 Localization} *)

type loc = int * int
let dloc = (-1,-1)
let mk_loc l c = (l,c)
let of_loc l = l

let path = ref []
let get_path () = !path
let add_path s = path := s :: !path

(** {2 Debugging} *)

module Debug = struct

  type flag  = ..
  type flag += D_warn | D_notice | D_module | D_typeChecking
            | D_rule | D_reduce | D_matching

  exception DebugMessageNotSet of flag

  let flag_message : (flag, string * bool) Hashtbl.t =
    Hashtbl.create 8
    
  let _ =
    Hashtbl.add flag_message D_warn         ("Warning"     , true);
    Hashtbl.add flag_message D_notice       ("Notice"      , false);
    Hashtbl.add flag_message D_module       ("Module"      , false);
    Hashtbl.add flag_message D_rule         ("Rule"        , false);
    Hashtbl.add flag_message D_typeChecking ("TypeChecking", false);
    Hashtbl.add flag_message D_reduce       ("Reduce"      , false);
    Hashtbl.add flag_message D_matching     ("Matching"    , false)

  let register_flag fl m =
    Hashtbl.replace flag_message fl (m,false)

  let is_active (fl : flag ) : bool =
    try
      snd (Hashtbl.find flag_message fl)
    with Not_found -> raise (DebugMessageNotSet fl)

  let message (fl : flag ) : string =
    try
      fst (Hashtbl.find flag_message fl)
    with Not_found -> raise (DebugMessageNotSet fl)
      
  let enable_flag fl =
    try
      let (s,_) = Hashtbl.find flag_message fl in
      Hashtbl.replace flag_message fl (s,true)
    with Not_found -> raise (DebugMessageNotSet fl)
    
  let disable_flag fl =
    try
      let (s,_) = Hashtbl.find flag_message fl in
      Hashtbl.replace flag_message fl (s,false)
    with Not_found -> raise (DebugMessageNotSet fl)

  let do_debug fmt =
    Format.(kfprintf (fun _ -> pp_print_newline err_formatter ()) err_formatter fmt)

  let ignore_debug fmt =
    Format.(ifprintf err_formatter) fmt

  let debug f =
    if is_active f
    then
      fun fmt -> do_debug ("[%s] " ^^ fmt) (message f)
    else ignore_debug
  [@@inline]

  let debug_eval f clos = if is_active f then clos ()

end

(** {2 Misc functions} *)

let bind_opt f = function
  | None -> None
  | Some x -> f x

let map_opt f = function
  | None -> None
  | Some x -> Some (f x)

let fold_map (f:'b->'a->('c*'b)) (b0:'b) (alst:'a list) : ('c list*'b) =
  let (clst,b2) =
    List.fold_left (fun (accu,b1) a -> let (c,b2) = f b1 a in (c::accu,b2))
      ([],b0) alst in
    ( List.rev clst , b2 )

let rec split_list i l =
  if i = 0 then ([],l)
  else
    let s1, s2 = split_list (i-1) (List.tl l) in
    (List.hd l)::s1, s2


(** {2 Printing functions} *)

type 'a printer = Format.formatter -> 'a -> unit

let string_of fp = Format.asprintf "%a" fp

let pp_ident  fmt id      = Format.fprintf fmt "%s" id
let pp_mident fmt md      = Format.fprintf fmt "%s" md
let pp_name   fmt (md,id) = Format.fprintf fmt "%a.%a" pp_mident md pp_ident id
let pp_loc    fmt = function
  | (-1,-1) -> Format.fprintf fmt "unspecified location"
  | (l ,-1) -> Format.fprintf fmt "line:%i" l
  | (l , c) -> Format.fprintf fmt "line:%i column:%i" l c

let format_of_sep str fmt () : unit = Format.fprintf fmt "%s" str

let pp_list sep pp fmt l = Format.pp_print_list ~pp_sep:(format_of_sep sep) pp fmt l
let pp_llist sep pp fmt l = pp_list sep pp fmt (LList.lst l)
let pp_arr  sep pp fmt a = pp_list sep pp fmt (Array.to_list a)
let pp_lazy pp fmt l = Format.fprintf fmt "%a" pp (Lazy.force l)

let pp_option def pp fmt = function
  | None   -> Format.fprintf fmt "%s" def
  | Some a -> Format.fprintf fmt "%a" pp a
