open Re_der

(* 1. Simple single-character regex *)
let r1 = Char 'a'

(* Test matches *)
let _ =
  assert (matches r1 "a");      (* true: 'a' matches "a" *)
  assert (not (matches r1 "")); (* false: cannot match empty string *)
  assert (not (matches r1 "b")); (* false: 'a' does not match "b" *)
  ()

(* Derive r1 w.r.t. 'a' and 'b' *)
let d1_a = derive r1 'a'  (* should be Epsilon, since "a" consumes 'a' *)
let d1_b = derive r1 'b'  (* should be Empty, since 'b' ≠ 'a' *)

let _ =
  assert (d1_a = Epsilon);
  assert (d1_b = Empty);
  ()

(* 2. Alternation: r2 = 'a' | 'b' *)
let r2 = alt (Char 'a') (Char 'b')

let _ =
  assert (matches r2 "a");      (* true *)
  assert (matches r2 "b");      (* true *)
  assert (not (matches r2 "c")); (* false *)
  assert (not (matches r2 ""));  (* false *)

  (* Derive r2 w.r.t. 'a' *)
  let d2_a = derive r2 'a' in
  (* derive (a|b) 'a' = alt (derive 'a' 'a') (derive 'b' 'a') 
       = alt Epsilon Empty = Epsilon *)
  assert (d2_a = Epsilon);

  (* Derive w.r.t. 'b' *)
  let d2_b = derive r2 'b' in
  (* alt (derive 'a' 'b') (derive 'b' 'b') = alt Empty Epsilon = Epsilon *)
  assert (d2_b = Epsilon);

  (* Derive w.r.t. 'c' *)
  let d2_c = derive r2 'c' in
  (* alt (Empty) (Empty) = Empty *)
  assert (d2_c = Empty);
  ()

(* 3. Sequence: r3 = "ab" (i.e., 'a' followed by 'b') *)
let r3 = seq (Char 'a') (Char 'b')

let _ =
  assert (matches r3 "ab");   (* true *)
  assert (not (matches r3 "a"));  (* false, missing 'b' *)
  assert (not (matches r3 "b"));  (* false, missing 'a' *)
  assert (not (matches r3 "abc")); (* false, extra 'c' *)

  (* Derive w.r.t. 'a' *)
  let d3_a = derive r3 'a' in
  (* Since nullable 'a' = false, derive = seq (derive 'a' 'a') 'b' 
       = seq Epsilon (Char 'b')  ≅ Char 'b' (via the smart constructor) *)
  assert (d3_a = Char 'b');

  (* Now derive that result w.r.t. 'b' *)
  let d3_ab = derive d3_a 'b' in
  (* derive (Char 'b') 'b' = Epsilon *)
  assert (d3_ab = Epsilon);

  (* And check nullable *)
  assert (nullable d3_ab);  (* true, since Epsilon matches "" *)

  (* Final membership test via derive_string *)
  let after_ab = derive_string r3 "ab" in
  assert (after_ab = Epsilon);
  assert (nullable after_ab); (* true, so matches "ab" *)
  ()

(* 4. Kleene star: r4 = ('a')* *)
let r4 = star (Char 'a')

let _ =
  assert (matches r4 "");       (* true: star always matches empty *)
  assert (matches r4 "a");      (* true *)
  assert (matches r4 "aaa");    (* true *)
  assert (not (matches r4 "b")); (* false *)

  (* Derive w.r.t. 'a' *)
  let d4_a = derive r4 'a' in
  (* derive (a*) 'a' = seq (derive 'a' 'a') (star (Char 'a')) 
       = seq Epsilon (star (Char 'a'))  ≅ star (Char 'a') *)
  assert (d4_a = r4);

  (* Derive w.r.t. 'b' *)
  let d4_b = derive r4 'b' in
  (* derive (a*) 'b' = seq (Empty) (star (Char 'a')) = Empty *)
  assert (d4_b = Empty);
  ()

(* 5. Alternation + concatenation + star: r5 = (a|b)* "c" *)
let r5 =
  seq
    (star (alt (Char 'a') (Char 'b')))
    (Char 'c')

(* Tests *)
let _ =
  assert (matches r5 "c");      (* ("" repeated from (a|b)*) then 'c' ⇒ true *)
  assert (matches r5 "ac");     (* "a" then "c" *)
  assert (matches r5 "bbac");   (* "bba" then "c" *)
  assert (not (matches r5 "")); (* no 'c' *)
  assert (not (matches r5 "a")); (* no 'c' *)
  assert (not (matches r5 "ab"));(* no 'c' *)

  (* Derive step-by-step on "abac" *)
  let after_a = derive r5 'a' in
  (* derive ( (a|b)* c ) 'a' 
       = seq (derive (a|b)* 'a') c           [ r1 = (a|b)* is nullable=true ]
         alt ( seq (derive (a|b)* 'a') (Char 'c') )
             (derive (Char 'c') 'a')
       = alt ( seq (r1) (Char 'c') ) Empty
       = seq (r1) (Char 'c')  (= (a|b)* c again)
  *)
  assert (after_a = r5);

  let after_ab = derive after_a 'b' in
  (* same logic: still r5 *)
  assert (after_ab = r5);

  let after_aba = derive after_ab 'a' in
  assert (after_aba = r5);

  (* Now derive final 'c' *)
  let after_abac = derive after_aba 'c' in
  (* derive r5 'c' 
       = alt ( seq (derive (a|b)* 'c') (Char 'c') ) (derive (Char 'c') 'c' )
       = alt ( seq Empty (Char 'c') ) Epsilon
       = alt Empty Epsilon = Epsilon
  *)
  assert (after_abac = Epsilon);
  assert (nullable after_abac); (* true, so matches "abac" *)
  ()


let r6 =
  and_ (star (Char 'a')) (seq (Char 'a') (star (Char 'a')))

let _ =
  assert (not (matches r6 ""));  (* false: second conjunct (a a*) does not allow "" *)
  assert (matches r6 "a");       (* true: both (a*) and (a a*) match "a" *)
  assert (matches r6 "aaaa");    (* true: both match any positive number of 'a's *)
  assert (not (matches r6 "b"));  (* false *)
  ()