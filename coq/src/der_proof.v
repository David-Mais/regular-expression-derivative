From Coq Require Import Ascii List Bool.
Import ListNotations.

(* A word is a finite list of symbols from Σ (here: ASCII) *)
Definition word := list ascii.

Inductive regex : Type :=
| Empty   : regex                      (* ∅ : empty language *)
| Epsilon : regex                      (* ε : language {ε} *)
| Char    : ascii -> regex             (* a ∈ Σ : singleton {a} *)
| Alt     : regex -> regex -> regex    (* r + s : union *)
| And     : regex -> regex -> regex    (* r & s : intersection *)
| Seq     : regex -> regex -> regex    (* r · s : concatenation *)
| Star    : regex -> regex             (* r* : Kleene star *)
| Neg     : regex -> regex.            (* ¬r : complement *)

(* Union: ∅ is neutral (∅ + r = r). Otherwise keep Alt. *)
Definition alt (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, r | r, Empty => r
  | _, _ => Alt r1 r2
  end.


(* Intersection: ∅ is absorbing (∅ & r = ∅). Otherwise keep And. *)
Definition and_ (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | _, _ => And r1 r2
  end.

(* Concatenation: ∅ is absorbing; ε is neutral (ε·r = r = r·ε). *)
Definition cat (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | Epsilon, r | r, Epsilon => r
  | _, _ => Seq r1 r2
  end.

(* Star: ∅* = ε and ε* = ε; collapse nested stars. *)
Definition star (r : regex) : regex :=
  match r with
  | Empty | Epsilon => Epsilon
  | Star r' => Star r'
  | _ => Star r
  end.

(* Complement: push negation using De Morgan; eliminate double negation. *) 
Definition neg(r : regex) : regex :=
  match r with
  | Neg r' => r'
  | Alt r1 r2 => and_ (Neg r1) (Neg r2)
  | And r1 r2 => alt (Neg r1) (Neg r2)
  | _ => Neg r
  end.

Fixpoint nullable (r : regex) : bool :=
  match r with
  | Empty        => false                      (* ε ∉ ∅ *)
  | Epsilon      => true                       (* ε ∈ {ε} *)
  | Char _       => false                      (* ε ∉ {a} *)
  | Alt r1 r2    => nullable r1 || nullable r2 (* ε ∈ L(r1) ∪ L(r2) *)
  | And r1 r2    => nullable r1 && nullable r2 (* ε ∈ L(r1) ∩ L(r2) *)
  | Seq r1 r2    => nullable r1 && nullable r2 (* ε ∈ L(r1)·L(r2) *)
  | Star _       => true                       (* ε ∈ L((r)*)
  | Neg r1       => negb (nullable r1)         (* ε ∈ ¬L(r) iff ε ∉ L(r) *)
  end.

(* Regex-valued ν(r): (returns ε or ∅)*)
Definition nu (r : regex) : regex :=
  if nullable r then Epsilon else Empty.


(* ------------------------------------------------------------------ *)
(* Semantics of regular expressions                                    *)
(* ------------------------------------------------------------------ *)

(* A language over Σ is represented as a membership predicate on words. *)
Definition language := word -> Prop.

(* Inductive (least) definition of Kleene star for an arbitrary language L.
   - star_nil: ε is in L*.
   - star_app: if u ∈ L and v ∈ L* then u ++ v ∈ L*.
   Here "++" is list (word) concatenation. *)
Inductive star_lang (L : language) : language :=
| star_nil  : star_lang L []
| star_app  : forall u v, L u -> star_lang L v -> star_lang L (u ++ v).

(*Lang maps a regex to its language, i.e. a predicate that, 
given a word, says whether that word is denoted by the regex.*)
Fixpoint Lang (r : regex) : language :=
  match r with
  | Empty     =>
      (* ∅ : no word is a member *)
      fun _ => False
  | Epsilon   =>
      (* {ε} : only the empty word is a member *)
      fun w => w = []
  | Char a    =>
      (* {a} : only the one-symbol word [a] is a member *)
      fun w => w = [a]
  | Alt r s   =>
      (* r + s : union of languages *)
      fun w => Lang r w \/ Lang s w
  | And r s   =>
      (* r & s : intersection of languages *)
      fun w => Lang r w /\ Lang s w
  | Seq r s   =>
      (* r · s : concatenation; w splits as u ++ v with u ∈ Lang r and v ∈ Lang s *)
      fun w => exists u v, w = u ++ v /\ Lang r u /\ Lang s v
  | Star r    =>
      (* r* : Kleene star of Lang r *)
      star_lang (Lang r)
  | Neg r     =>
      (* ¬r : complement of Lang r (relative to all words) *)
      fun w => ~ Lang r w
  end.

(* ------------------------------------------------------------------ *)
(* Derivative on languages - Semantic                                 *)
(* ------------------------------------------------------------------ *)

(*Semantic derivative with respect to a single character*)
Definition dlang_char (a : ascii) (L : language) : language :=
  fun w => L (a :: w).

(*Semantic derivative with respect to a word*)
Fixpoint dlang (u : word) (L : language) : language :=
  match u with
  | []     => L
  | a :: v => dlang v (dlang_char a L)
  end.

(* ------------------------------------------------------------------ *)
(* Derivative on regex - Syntactic                                    *)
(* ------------------------------------------------------------------ *)

Definition ascii_eq_dec := Ascii.ascii_dec.

(*Syntactic derivative with respect to a single character*)
Fixpoint D_char (a : ascii) (r : regex) : regex :=
  match r with
  | Empty      => Empty   (* D_a(∅) = ∅ : no word in ∅ starts with a *)
  | Epsilon    => Empty   (* D_a({ε}) = ∅ : ε does not start with a *)
  | Char c     => if ascii_eq_dec a c then Epsilon else Empty    (* D_a({c}) = {ε} if a = c, else ∅ *)
  | Alt r s    => Alt (D_char a r) (D_char a s)    (* D_a(r + s) = D_a(r) + D_a(s) : derivative distributes over union *)
  | And r s    => And (D_char a r) (D_char a s)    (* D_a(r & s) = D_a(r) & D_a(s) : derivative distributes over intersection *)
  | Seq r s    => Alt (Seq (D_char a r) s) (Seq (nu r) (D_char a s)) 
      (* Concatenation rule:
         D_a(r · s) = D_a(r) · s  +  ν(r) · D_a(s)
         - First term: a is consumed by the left factor r, remainder must still match s.
         - Second term: if r is nullable (ν(r)=ε), a can be consumed by s. *)
  | Star r     => Seq (D_char a r) (Star r)     (* D_a(r* = D_a(r) · r* : first block comes from r, rest stays in r* *)
  | Neg r      => Neg (D_char a r)       (* D_a(¬r) = ¬(D_a(r)) : complement commutes with left quotient *)
  end.

(*Syntactic derivative with respect to a word*)
Fixpoint D (u : word) (r : regex) : regex :=
  match u with
  | []     => r
  | a :: v => D v (D_char a r)
  end.

(* ------------------------------------------------------------------ *)
(* Nullability correctness                                              *)
(* ------------------------------------------------------------------ *)

(* nullable_correct: the boolean test nullable r is true exactly when r accepts ε
   (i.e., Lang r [] holds). 
   so when nullable r is true language denoted by r contains the empty word *)
Lemma nullable_correct : forall r, nullable r = true <-> Lang r [].
Proof.
  induction r; simpl. (*divide iff into two goals*)
  (*r = Empyy | nullable Empty = true -> Lang Empty [], false = true, discriminate solves impossible equalities
  Lang Empty [] is False. and inversion closes contradictions| *)
  - split; [discriminate | intro H; inversion H].
  (*r = Epsilon, trivial true = true*)
  - split; [reflexivity | intro H; now subst].
  (*r = Char _*)
  - split; [discriminate | intro H; inversion H].
  - (* Alt *)
    rewrite Bool.orb_true_iff.
    split.
    + intros [H|H]; [left; apply IHr1 in H | right; apply IHr2 in H]; assumption.
    + intros [Hr|Hs]; [left; apply (proj2 IHr1) in Hr | right; apply (proj2 IHr2) in Hs]; assumption.
  - (* And *)
    rewrite Bool.andb_true_iff.
    split.
    + intros [H1 H2]; split; [apply IHr1 in H1 | apply IHr2 in H2]; assumption.
    + intros [Hr Hs]; split; [apply (proj2 IHr1) in Hr | apply (proj2 IHr2) in Hs]; assumption.
  - (* Seq *)
    rewrite Bool.andb_true_iff.
    split.
    + intros [H1 H2].
      apply IHr1 in H1. apply IHr2 in H2.
      exists [], []; repeat split; auto.
    + intros [u [v [Huv [Hu Hv]]]].
      symmetry in Huv.
      apply app_eq_nil in Huv as [-> ->].
      split; [apply (proj2 IHr1) in Hu | apply (proj2 IHr2) in Hv]; assumption.
    - (* Star *)
    split.
    + intros _. constructor.
    + intros _. reflexivity.
  - (* Neg *)
    rewrite Bool.negb_true_iff.
    split.
    + intros Hneg Hr. apply (proj2 IHr) in Hr. now rewrite Hr in Hneg.
    + intro Hnot. destruct (nullable r) eqn:E.
      * exfalso. apply Hnot. apply (proj1 IHr). reflexivity. 
      * reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Correctness of derivatives                                          *)
(* ------------------------------------------------------------------ *)

(* star_cons_split:
   If a word s is in L* (star_lang L s) and s starts with the letter a
   (so s = a :: w), then we can "peel" that leading a into the first block
   coming from L. Concretely, there exist u and v such that:
     w = u ++ v,
     L (a :: u)          (the first block from L begins with that a),
     star_lang L v.      (the remainder stays in L-star).
   Intuition: a proof that s ∈ L* is built by concatenating blocks u₁,u₂,… ∈ L.
   If u₁ is empty, skip it and look at the tail; if u₁ = a::u, then we’re done. *)

Lemma star_cons_split :
  forall (L : language) (s : word),
    star_lang L s ->
    forall (a : ascii) (w : word),
      s = a :: w ->
      exists u v, w = u ++ v /\ L (a :: u) /\ star_lang L v.
Proof.
  intros L s H.
  induction H as [| u v Lu Hv IH].
  - (* s = [] *) intros a w Heq; discriminate Heq.
  - (* s = u ++ v with Lu : L u and Hv : star_lang L v *)
    intros a w Heq.
    destruct u as [| a' u'].
    + (* u = [] ⇒ s = v *) simpl in Heq. eapply IH; eauto.
    + (* u = a' :: u' *)
      simpl in Heq. inversion Heq; subst.
      (* now a' = a and w = u' ++ v *)
      exists u', v. repeat split; auto.
Qed.
(*  *)

Lemma D_char_correct :
  forall a r w, Lang (D_char a r) w <-> Lang r (a :: w).
Proof.
  induction r; intros w; simpl.
  - tauto.
  - split; [tauto| intros H; inversion H].
  - destruct (ascii_eq_dec a a0) as [->|neq]; simpl; firstorder congruence.
  - specialize (IHr1 w). specialize (IHr2 w). tauto.
  - specialize (IHr1 w). specialize (IHr2 w). tauto.
  - (* Seq *)
    split.
    + intros H; destruct H as [H|H].
      * destruct H as [u [v [Hw [Hu Hv]]]]. subst w.
        exists (a :: u), v. split; [reflexivity|].
        split; [apply IHr1 in Hu; exact Hu | exact Hv].
      * destruct H as [u [v [Hw [Hnu Hv]]]]. subst w.
        unfold nu in Hnu.
        destruct (nullable r1) eqn:En; simpl in Hnu.
        -- apply nullable_correct in En. simpl in Hnu. subst u.
           exists [], (a :: v). split; [reflexivity|].
           split; [exact En | apply IHr2 in Hv; exact Hv].
        -- contradiction.
    + intros [u [v [Huv [Hur Hvr]]]].
      destruct u as [|a' u'].
      * simpl in Huv. right.
        exists [], w. split; [reflexivity|].
        split.
        { unfold nu. apply (proj2 (nullable_correct r1)) in Hur. now rewrite Hur. }
        { rewrite <- Huv in Hvr. apply IHr2. exact Hvr. }
      * inversion Huv as [Htail]. subst a' w.
        left. exists u', v. split; [reflexivity|].
        split; [apply IHr1; exact Hur | exact Hvr].
  - (* Star *)
    split.
    + (* -> *)
      intros [u [v [Hw [Hud Hsv]]]].
      subst w. specialize (IHr u). apply IHr in Hud.
      change (star_lang (Lang r) ((a :: u) ++ v)).
      apply star_app; [assumption|assumption].
    + (* <- *)
      intros Hstar.
      edestruct (star_cons_split (Lang r) (a :: w) Hstar)
        as [u [v [Hw' [Lu Hv']]]]; [reflexivity|].
      exists u, v. split; [exact Hw'|].
      split; [apply IHr; exact Lu | exact Hv'].
  - (* Neg *)
    split; intro H.
    + intro Hr0. apply H. apply IHr. exact Hr0.
    + intro Hr0. apply H. apply IHr. exact Hr0.
Qed.


(* Word derivative correctness by induction on u *)
Lemma D_correct :
  forall u r w, Lang (D u r) w <-> Lang r (u ++ w).
Proof.
  induction u as [| a v IHv]; intros r w; simpl.
  - tauto.
  - rewrite IHv. apply D_char_correct.
Qed.

(* ------------------------------------------------------------------ *)
(* Regular languages and Theorem 4.1                                   *)
(* ------------------------------------------------------------------ *)

Definition regular (L : language) : Prop :=
  exists r, forall w, Lang r w <-> L w.

(* helper: semantics of dlang *)
Lemma dlang_correct :
  forall (u : word) (L : language) (w : word),
    dlang u L w <-> L (u ++ w).
Proof.
  induction u as [|a v IHv]; intros L w; simpl.
  - tauto.
  - rewrite IHv. unfold dlang_char. simpl. tauto.
Qed.

Theorem derivative_regular :
  forall (L : language) (u : word),
    regular L -> regular (dlang u L).
Proof.
  intros L u [r Hr].
  exists (D u r). intro w.
  split.
  - (* -> *)
    intro H.                             (* Lang (D u r) w *)
    apply D_correct in H.                (* Lang r (u ++ w) *)
    apply (proj1 (Hr (u ++ w))) in H.    (* L (u ++ w) *)
    apply (proj2 (dlang_correct u L w)); exact H.
  - (* <- *)
    intro H.                             (* dlang u L w *)
    apply (proj1 (dlang_correct u L w)) in H.  (* L (u ++ w) *)
    apply (proj2 (Hr (u ++ w))) in H.          (* Lang r (u ++ w) *)
    apply D_correct; exact H.                  (* Lang (D u r) w *)
Qed.