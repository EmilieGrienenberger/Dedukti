open Types

let marshal deps env =
  try
    begin
      let out = open_out (string_of_ident !Global.name ^ ".dko" ) in
        Marshal.to_channel out Global.version [] ;
        Marshal.to_channel out deps [] ;
        Marshal.to_channel out env [Marshal.Closures] ;
        close_out out
    end
  with
    | _ -> Global.fail dloc "Fail to export module '%a'." pp_ident !Global.name

exception BadVersionNumber

let unmarshal (lc:loc) (m:string) =
  try
    begin
      let chan = open_in ( m ^ ".dko" ) in
      let ver:string = Marshal.from_channel chan in
        if String.compare ver Global.version = 0 then
          begin
            let deps:string list = Marshal.from_channel chan in
            let ctx:rw_infos H.t = Marshal.from_channel chan in
              close_in chan ; (deps,ctx)
          end
        else raise BadVersionNumber
    end
  with
    | BadVersionNumber -> Global.fail lc "Fail to open\
module '%s' (file generated by a different version?)." m
    | Sys_error s -> Global.fail lc "Fail to open module '%s' (%s)." m s
    | _ -> Global.fail lc "Fail to open module '%s'." m

module S = Set.Make (
struct
  type t = string
  let compare = String.compare
end )

let get_rules ctx : rule list =
  let lst_lst =
    H.fold (fun _ infos lst ->
              match infos with
                | Decl_rw (_,rs,_,_) -> rs::lst
                | _ -> lst
    ) ctx []
  in List.flatten lst_lst

let get_all_rules (md:string) : (string*rule list) list =
  let set = S.empty in
  let rec load = function
    | [] -> []
    | m::lst ->
        if S.mem m set then load lst
        else
          begin
            let (deps,ctx) = unmarshal dloc m in
              (m,ctx)::(load (List.rev_append lst deps))
          end
  in
    List.rev_map (fun (m,ctx) -> (m,get_rules ctx)) (load [md])