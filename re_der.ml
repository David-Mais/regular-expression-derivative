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
  let alphabet = List.init 256 Char.chr in

  let rec bfs current_len list_of_pairs acc_words =
    let acc_words' =
      if current_len = 0 then
        if nullable r then "" :: acc_words else acc_words
      else
        List.fold_left
          (fun acc (w, dreg) ->
            if nullable dreg then w :: acc else acc)
          acc_words
          list_of_pairs
    in

    if current_len = max_len then
      acc_words'
    else
      let next_pairs =
        List.concat (
          List.map
            (fun (w, dreg) ->
              List.fold_left
                (fun acc c ->
                  let d' = derive dreg c in
                  if d' <> Empty then
                    (w ^ String.make 1 c, d') :: acc
                  else
                    acc)
                []
                alphabet
            )
            list_of_pairs
        )
      in
      bfs (current_len + 1) next_pairs acc_words'
  in

  bfs 0 [("", r)] []

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


(*----------------------------------------------------------------*)
(* === Global similarity table === *)

(* We keep one global Hashtbl mapping (char * char) -> float,
   storing a number in [0.0; 1.0] that measures how “close” two chars are. *)
let similarity_table : ((char * char), float) Hashtbl.t = Hashtbl.create 256

(* To populate or update the table:
     set_similarity 'a' 'b' 0.6
   means that 'a'–'b' have similarity 0.6. We also store symmetrically
   so that similarity c1 c2 = similarity c2 c1. *)
let set_similarity (c1 : char) (c2 : char) (sim : float) : unit =
  if sim < 0.0 || sim > 1.0 then
    invalid_arg "set_similarity: sim must be in [0.,1.]"
  else begin
    Hashtbl.replace similarity_table (c1, c2) sim;
    Hashtbl.replace similarity_table (c2, c1) sim
  end

(* Look up similarity.  If the two characters are exactly equal, return 1.0.
   Otherwise, check the table; default is 0.0 if not present. *)
let similarity (c1 : char) (c2 : char) : float =
  if c1 = c2 then 1.0
  else
    match Hashtbl.find_opt similarity_table (c1, c2) with
    | Some sim -> sim
    | None     -> 0.0


(*----------------------------------------------------------------*)
(* fuzzy_derive  :  regex -> char -> float -> regex
   “Threshold” is the minimum similarity required to treat (c vs d) as a match. *)

let rec fuzzy_derive (r : regex) (c : char) (threshold : float) : regex =
  match r with
  | Empty ->
      Empty

  | Epsilon ->
      Empty

  | Char d ->
      (* Instead of (if d = c then Epsilon else Empty), we check similarity. *)
      if similarity c d >= threshold
      then
        Epsilon
      else
        Empty

  | Alt (r1, r2) ->
      (* Just distribute over alternation *)
      alt (fuzzy_derive r1 c threshold)
          (fuzzy_derive r2 c threshold)

  | And (r1, r2) ->
      (* Distribute over intersection *)
      and_ (fuzzy_derive r1 c threshold)
           (fuzzy_derive r2 c threshold)

  | Seq (r1, r2) ->
      (* If r1 can be nullable, we have two options (like ordinary derivative). *)
      if nullable r1 then
        alt
          (seq   (fuzzy_derive r1 c threshold) r2)
          (fuzzy_derive r2 c threshold)
      else
        seq (fuzzy_derive r1 c threshold) r2

  | Star r' ->
      (* Same pattern as ordinary derivative of star *)
      seq (fuzzy_derive r' c threshold) (Star r')

(*----------------------------------------------------------------*)
(* “Fuzzy” derive‐over‐a‐string and “fuzzy” matches *)

(* Walk through the string, taking a fuzzy derivative at each step. *)
let fuzzy_derive_string (r : regex) (s : string) (threshold : float) : regex =
  String.fold_left (fun acc_reg ch -> fuzzy_derive acc_reg ch threshold) r s

(* Fuzzy membership test: after taking successive fuzzy derivatives,
   check nullable. *)
let fuzzy_matches (r : regex) (s : string) (threshold : float) : bool =
  let r' = fuzzy_derive_string r s threshold in
  nullable r'