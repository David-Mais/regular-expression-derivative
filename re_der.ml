(* Define the regular-expression datatype *)
type regex =
  | Empty                    (* matches no string *)
  | Epsilon                  (* matches the empty string "" *)
  | Char of char             (* matches one specific character *)
  | Alt of regex * regex     (* r1 | r2 *)
  | And of regex * regex     (* r1 & r2 *)
  | Seq of regex * regex     (* r1 r2 *)
  | Star of regex            (* r* *)

(* Smart constructors that simplify trivial cases *)
let alt r1 r2 = match r1, r2 with
  | Empty, r | r, Empty -> r
  | _ -> if r1 = r2 then r1 else Alt (r1,r2)

let and_ r1 r2 = match r1, r2 with
  | Empty, _ | _, Empty -> Empty
  | _ -> if r1 = r2 then r1 else And (r1, r2)

let seq r1 r2 = match r1, r2 with
  | Empty, _ | _, Empty -> Empty
  | Epsilon, r | r, Epsilon -> r
  | _ -> Seq (r1,r2)

let star r = match r with
  | Empty | Epsilon -> Epsilon
  | Star r' -> Star r'
  | _ -> Star r

(* Nullability: can this regex match the empty string? *)
let rec nullable = function
  | Empty -> false
  | Epsilon -> true
  | Char _ -> false
  | Alt (r1,r2) -> nullable r1 || nullable r2
  | And (r1, r2) -> nullable r1 && nullable r2
  | Seq (r1,r2) -> nullable r1 && nullable r2
  | Star _ -> true

(* Derivative of a regex w.r.t. character c *)
let rec derive r c = match r with
  | Empty -> Empty
  | Epsilon -> Empty
  | Char d -> if d = c then Epsilon else Empty
  | Alt (r1,r2) -> alt (derive r1 c) (derive r2 c)
  | And (r1, r2) -> and_ (derive r1 c) (derive r2 c)
  | Seq (r1,r2) ->
      if nullable r1 then
        alt (seq (derive r1 c) r2) (derive r2 c)
      else
        seq (derive r1 c) r2
  | Star r' -> seq (derive r' c) (Star r')

(* Derivative of a regex w.r.t. string s *)
let derive_string r s =
  String.fold_left derive r s

(* Test membership: does regex r accept string s? *)
let matches r s =
  let r' = String.fold_left (fun acc ch -> derive acc ch) r s in
  nullable r'

(* Enumerate language up to length n (may be infinite for stars!) *)
let generate r max_len =
  let rec aux current_len words =
    if current_len > max_len then []
    else
      let rec extend prefix = function
        | [] -> [prefix]
        | cs ->
          List.concat_map (fun c ->
            let d = derive r c in
            if nullable d then [prefix ^ String.make 1 c] else []
          ) cs
      in
      let candidates =
        if current_len = 0 then
          if nullable r then [""] else []
        else
          List.concat_map (fun w -> extend w (List.init 256 Char.chr))
            (aux (current_len - 1) words)
      in
      words @ candidates
  in
  aux 0 []

(* Convert regex AST to a string for display *)
let rec show_regex = function
  | Empty        -> "∅"
  | Epsilon      -> "ε"
  | Char c       -> Printf.sprintf "%c" c
  | Alt (r1, r2) -> Printf.sprintf "%s|%s" (show_regex r1) (show_regex r2)
  | And (r1, r2) -> Printf.sprintf "%s&%s" (show_regex r1) (show_regex r2)
  | Seq (r1, r2) -> Printf.sprintf "%s%s"  (show_regex r1) (show_regex r2)
  | Star r       -> Printf.sprintf "(%s)*" (show_regex r)

(* Pretty-printer for utop: use Format.formatter -> regex -> unit *)
let pp_regex fmt r =
  Format.fprintf fmt "%s" (show_regex r)