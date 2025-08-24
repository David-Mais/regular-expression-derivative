Require Import Ascii.
Require Import List.
Import ListNotations.
Require Import Bool.

Definition string := list ascii.

Inductive regex : Type :=
| Empty : regex
| Epsilon : regex
| Char : ascii -> regex
| Alt : regex -> regex -> regex
| And : regex -> regex -> regex
| Seq : regex -> regex -> regex
| Star : regex -> regex
| Neg : regex -> regex.

Definition alt (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, r | r, Empty => r
  | _, _ => Alt r1 r2
  end.

Definition and_ (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | _, _ => And r1 r2
  end.

Definition cat (r1 r2 : regex) : regex :=
  match r1, r2 with
  | Empty, _ | _, Empty => Empty
  | Epsilon, r | r, Epsilon => r
  | _, _ => Seq r1 r2
  end.

Definition star (r1 : regex) : regex :=
  match r1 with
  | Empty | Epsilon => Epsilon
  | Star r => Star r
  | _ => Star r1
  end.

Definition neg(r1 : regex) : regex :=
  match r1 with
  | Neg r => r
  | Alt r r' => and_ (Neg r) (Neg r')
  | And r r' => alt (Neg r) (Neg r')
  | _ => Neg r1
  end.

Fixpoint nullable (r : regex) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Char _ => false
  | Alt r1 r2 => nullable r1 || nullable r2
  | And r1 r2 => nullable r1 && nullable r2
  | Seq r1 r2 => nullable r1 && nullable r2
  | Star _ => true
  | Neg r1 => negb (nullable r1)
  end.


(* Languages *)

Definition language := string -> Prop.

Inductive kstar (L : language) : language :=
| ks_eps : kstar L []
| ks_app : forall u v, L u -> kstar L v -> kstar L (u ++ v).

(*language denoted by some regex*)
Fixpoint denote (r : regex) : language :=
  match r with
  | Empty      => fun _ => False
  | Epsilon    => fun w => w = []
  | Char a     => fun w => w = [a]
  | Alt r1 r2  => fun w => denote r1 w \/ denote r2 w
  | And r1 r2  => fun w => denote r1 w /\ denote r2 w
  | Seq r1 r2  => fun w => exists u v, w = u ++ v /\ denote r1 u /\ denote r2 v
  | Star r1    => kstar (denote r1)
  | Neg r1     => fun w => ~ denote r1 w
  end.

Notation "⟦ r ⟧" := (denote r) (at level 9).

(** Regular languages: denoted by some regex *)
Definition regular (L : language) : Prop :=
  exists r, forall w, L w <-> ⟦r⟧ w.


(** * Semantic derivatives (languages) *)
(*derivative of a language with respect to a symbol*)
Definition dlang_sym (a : ascii) (L : language) : language :=
  fun w => L (a :: w).

Fixpoint dlang_word (u : string) (L : language) : language :=
  match u with
  | [] => L
  | a :: v => dlang_word v (dlang_sym a L)
  end.


(** derivative of a language with respect to string u without recursion *)
Definition dlang_word_concat (u : string) (L : language) : language :=
  fun w => L (u ++ w).

(** Proving that last two definitions are the same *)
Lemma dlang_equiv :
  forall u L w, dlang_word u L w <-> dlang_word_concat u L w.
Proof.
  induction u as [|a v IHv]; cbn; intro L; intro w.
  - tauto.
  - rewrite IHv. reflexivity.
Qed.

(*** ------------------------------------------------------------- ***)
(** * Nullable correctness (boolean-to-Prop bridge) *)

(* Lemma orb_true_iff : forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. destruct b1, b2; simpl; tauto. Qed.

Lemma andb_true_iff : forall b1 b2, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof. destruct b1, b2; simpl; tauto. Qed.

Lemma negb_true_iff : forall b, negb b = true <-> b = false.
Proof. destruct b; simpl; tauto. Qed.

Lemma nullable_correct : forall r, nullable r = true <-> ⟦r⟧ [].
Proof.
  induction r; simpl.
  - split; intros H; [discriminate|contradiction].
  - split; intros _; reflexivity.
  - split; intros H; [discriminate|].
    intros Hc. inversion Hc.
  - rewrite orb_true_iff, IHr1, IHr2. tauto.
  - rewrite andb_true_iff, IHr1, IHr2. tauto.
  - rewrite andb_true_iff, IHr1, IHr2. tauto.
  - split; intros _; constructor.
  - rewrite negb_true_iff, IHr. split.
    + intros Hb Hden. rewrite <- Hb in Hden. simpl in Hden. contradiction.
    + intros Hn. destruct (nullable r); [exfalso|reflexivity].
      apply IHr in eq_refl. contradiction.
Qed.

Lemma nullable_false_iff : forall r, nullable r = false <-> ~ ⟦r⟧ [].
Proof.
  intro r. rewrite <- Bool.not_true_iff_false, nullable_correct. tauto.
Qed. *)

(*** ------------------------------------------------------------- ***)
(** * Brzozowski derivative (syntactic) *)

Require Import Ascii.
Definition ascii_eq_dec := ascii_dec.

Fixpoint deriv_sym (a : ascii) (r : regex) : regex :=
  match r with
  | Empty      => Empty
  | Epsilon    => Empty
  | Char b     => if ascii_eq_dec a b then Epsilon else Empty
  | Alt r1 r2  => alt (deriv_sym a r1) (deriv_sym a r2)
  | And r1 r2  => and_ (deriv_sym a r1) (deriv_sym a r2)
  | Seq r1 r2  =>
      alt (cat (deriv_sym a r1) r2)
          (if nullable r1 then deriv_sym a r2 else Empty)
  | Star r1    => cat (deriv_sym a r1) (Star r1)
  | Neg r1     => neg (deriv_sym a r1)
  end.

Fixpoint deriv_word (u : string) (r : regex) : regex :=
  match u with
  | [] => r
  | a :: v => deriv_word v (deriv_sym a r)
  end.

(*** ------------------------------------------------------------- ***)
(** * List/Kleene-star lemmas used in correctness proof *)


Require Import List.
Import ListNotations.

Lemma kstar_cons_decomp :
  forall (L : language) a w,
    kstar L (a :: w) ->
    exists u v, u <> [] /\ L u /\ kstar L v /\ a :: w = u ++ v.
(* Proof.
  intros L a w H.
  (* Remember z = a :: w so we can generalize a, w, and the equation
     before we do induction on H. *)
  remember (a :: w) as z eqn:Hz.
  revert a w Hz.
  (* Induct on the derivation H : kstar L z *)
  induction H as [|u v Hu Hkv IH]; intros a w Hz.
  - (* ks_eps: kstar L [] *) discriminate Hz.
  - (* ks_app: H = ks_app u v Hu Hkv, so z = u ++ v *)
    (* split on whether the first chunk u is empty *)
    destruct u as [|x xs].
    + (* u = []: then z = [] ++ v, i.e., z = v *)
      simpl in Hz. rewrite app_nil_l in Hz.  (* so Hz: a :: w = v *)
      (* apply IH to the tail v *)
      specialize (IH a w Hz).
      destruct IH as (u' & v' & Hnz & Hu' & Hv' & Heq).
      now eexists; eexists; repeat (split; eauto).
    + (* u = x :: xs: nonempty first chunk *)
      exists (x :: xs), v.
      repeat split; eauto.
      * discriminate.             (* u <> [] *)
      * exact Hz.                  (* a :: w = (x :: xs) ++ v *)
Qed. *)







Lemma denote_alt : forall r1 r2 w,
  ⟦alt r1 r2⟧ w <-> (⟦r1⟧ w \/ ⟦r2⟧ w).
Proof.
  intros r1 r2 w. unfold alt.
  destruct r1; destruct r2; simpl; tauto.
Qed.

Lemma denote_and_ : forall r1 r2 w,
  ⟦and_ r1 r2⟧ w <-> (⟦r1⟧ w /\ ⟦r2⟧ w).
Proof.
  intros r1 r2 w. unfold and_.
  destruct r1; destruct r2; simpl; tauto.
Qed.


Lemma eps_left :
  forall (r : regex) (w : string),
    ⟦r⟧ w <-> (exists u v, w = u ++ v /\ ⟦Epsilon⟧ u /\ ⟦r⟧ v).
Proof.
  intros r w; split.
  - (* -> *)
    intro H. exists [], w. repeat split; try reflexivity; exact H.
  - (* <- *)
    intros (u & v & Hw & Hu & Hv).
    simpl in Hu.                    (* ⟦Epsilon⟧ u  is  u = [] *)
    subst u.                        (* replace u by [] *)
    rewrite app_nil_l in Hw.        (* w = [] ++ v  ⇒  w = v *)
    subst w. exact Hv.
Qed.

Lemma eps_right :
  forall (r : regex) (w : string),
    ⟦r⟧ w <-> (exists u v, w = u ++ v /\ ⟦r⟧ u /\ ⟦Epsilon⟧ v).
Proof.
  intros r w; split.
  - (* -> *)
    intro H.
    exists w, [].
    (* we must build w = w ++ [], ⟦r⟧ w, and ⟦Epsilon⟧ [] *)
    repeat split.
    + now rewrite app_nil_r.
    + exact H.
    + reflexivity.    (* since ⟦Epsilon⟧ v means v = [] *)
  - (* <- *)
    intros (u & v & Hw & Hu & Hv).
    simpl in Hv.      (* Hv : v = [] *)
    subst v.
    rewrite app_nil_r in Hw.
    subst w.
    exact Hu.
Qed.



Lemma denote_cat :
  forall r1 r2 w,
    ⟦cat r1 r2⟧ w <-> (exists u v, w = u ++ v /\ ⟦r1⟧ u /\ ⟦r2⟧ v).
Proof.
  intros r1 r2 w. unfold cat.
  destruct r1; destruct r2; simpl.

  (* Any branch where cat reduces to Empty: left side is False *)
  all: try (split; intro H;
            [ contradiction
            | destruct H as [u [v [_ [Hu _]]]]; exact Hu ]).

  (* Left Epsilon (and right not Empty): use eps_left *)
  all: try (apply eps_left).

  (* Right Epsilon (and left not Empty): use eps_right *)
  all: try (apply eps_right).

  (* Remaining branches: cat left as Seq r1 r2; both sides identical by ⟦Seq⟧ def *)
  all: apply iff_refl.
Qed.





(*** ------------------------------------------------------------- ***)
(** * Semantic–syntactic correspondence for one symbol *)

Theorem deriv_sym_correct :
  forall (r : regex) (sym : ascii) (w : string),
    ⟦deriv_sym sym r⟧ w <-> ⟦r⟧ (sym :: w).
Proof.
  intros r sym w; revert sym w.
  induction r as
    [ (* Empty *)
    | (* Epsilon *)
    | b
    | r1 IH1 r2 IH2
    | r1 IH1 r2 IH2
    | r1 IH1 r2 IH2
    | r1 IH1
    | r1 IH1
    ]; intros sym w; simpl.
  - tauto.
  - simpl; split; [tauto | now intros Heq; discriminate].
  (* Char b *)
  - destruct (ascii_eq_dec sym b) as [->|Hb]; simpl; split; intro H.
  (* sym = b, -> direction: w = [] -> b :: w = [b] *)
    now subst.
  (* sym = b, <- direction: b :: w = [b] -> w = [] *)
    now inversion H.
  (* sym <> b, -> direction: False -> sym :: w = [b] *)
    contradiction.
  (* sym <> b, <- direction: sym :: w = [b] -> False *)
    inversion H; congruence.
  - (* Alt *)
    rewrite denote_alt. simpl. rewrite IH1, IH2. tauto.
  - (* And *)
    rewrite denote_and_. simpl. rewrite IH1, IH2. tauto.
  - (* Seq *)
    rewrite denote_alt. simpl.
    split.
    + (* -> *)
      intros [Hleft | Hright].
      * (* left branch: seq (deriv r1) r2 *)
        rewrite denote_seq in Hleft.
        destruct Hleft as [u [v [Hw [Hu Hv]]]]. subst w.
        exists (sym :: u), v. repeat split; eauto.
        -- (* ⟦r1⟧ (sym :: u) *)
           apply IH1. exact Hu.
        -- (* a :: (u ++ v) equals (a :: u) ++ v *)
           reflexivity.
      * (* right branch: nullable r1 and deriv on r2 *)
        destruct (nullable r1) eqn:En; [|contradiction].
        apply nullable_correct in En.
        (* Hright : ⟦deriv_sym sym r2⟧ w *)
        exists [], (sym :: w). repeat split; eauto.
        -- reflexivity.
        -- exact En.
        -- apply IH2. exact Hright.
    + (* <- *)
      intros [u [v [Heq [Hr1u Hr2v]]]].
      destruct (u) as [|x xs].
      * (* u = []: use right branch *)
        right.
        assert (nullable r1 = true) as En.
        { apply nullable_correct. simpl in Hr1u. now subst. }
        rewrite En. simpl.
        replace (sym :: v) with (sym :: w).
        -- apply IH2. assumption.
        -- now simpl in Heq.
      * (* u = x::xs: use left branch *)
        left.
        (* from a::w = (x::xs) ++ v we get sym = x and w = xs ++ v *)
        simpl in Heq. inversion Heq; subst x w.
        rewrite denote_seq. exists xs, v. repeat split; eauto.
        -- apply IH1. assumption.
  - (* Star *)
    rewrite denote_seq. simpl.
    split.
    + (* ->: build kstar by consing the first chunk *)
      intros [u [v [Hw [Hdu Hkv]]]]. subst w.
      apply IH1 in Hdu. (* ⟦r1⟧ (sym :: u) *)
      (* Build kstar ⟦r1⟧ ((sym :: u) ++ v) = kstar ⟦r1⟧ (sym :: (u ++ v)) *)
      remember (sym :: u) as first.
      assert (kstar ⟦r1⟧ (first ++ v)) as Hks by (apply ks_app; assumption).
      (* rewrite (sym :: u) ++ v = sym :: (u ++ v) *)
      now simpl in Hks.
    + (* <-: decompose nonempty kstar head *)
      intro H.
      (* from kstar ⟦r1⟧ (sym :: w) get first nonempty chunk u *)
      destruct (kstar_cons_decomp ⟦r1⟧ sym w H)
        as (u & v & Hnz & Hu & Hv & Heq).
      (* u must start with sym *)
      destruct u as [|x xs]; [contradiction|].
      simpl in Heq. inversion Heq; subst x w.
      (* Build the Seq witness: w = xs ++ v *)
      exists xs, v. repeat split; eauto.
      apply IH1. exact Hu.
  - (* Neg *)
    split; intro H.
    + (* -> : ⟦Neg (deriv_sym sym r1)⟧ w  ->  ~⟦r1⟧ (sym::w) *)
      intro K. apply H. apply IH1. exact K.
    + (* <- : ~⟦r1⟧ (sym::w)  ->  ⟦Neg (deriv_sym sym r1)⟧ w *)
      intro K. apply H. apply IH1. exact K.
Qed.


(*** ------------------------------------------------------------- ***)
(** * Semantic–syntactic correspondence for a word *)

Theorem deriv_word_correct :
  forall (r : regex) (u : string) (w : string),
    ⟦deriv_word u r⟧ w <-> dlang_word u ⟦r⟧ w.
Proof.
  intros r u w.
  revert r.
  induction u as [|a v IHv]; intros r; simpl.
  - tauto.
  - (* u = a :: v *)
    (* Use IH instantiated at r' = deriv_sym a r *)
    rewrite (IHv (deriv_sym a r)).
    (* Now switch both sides to the concat form with dlang_equiv *)
    rewrite (dlang_equiv v ⟦deriv_sym a r⟧ w).
    rewrite (dlang_equiv v (dlang_sym a ⟦r⟧) w).
    (* Finally, apply the 1-symbol correspondence at w' = v ++ w *)
    apply deriv_sym_correct.
Qed.



(*** ------------------------------------------------------------- ***)
(** * Theorem 4.1: Derivative of a regular language is regular *)

Theorem derivative_preserves_regular :
  forall (L : language) (u : string),
    regular L -> regular (dlang_word u L).
Proof.
  intros L u [r Hr].              (* L ≡ ⟦r⟧ *)
  exists (deriv_word u r). intro w.
  rewrite deriv_word_correct.     (* ⟦D_u r⟧ w <-> dlang_word u ⟦r⟧ w *)
  (* Replace ⟦r⟧ using regularity witness Hr *)
  revert r Hr. induction u as [|a v IHv]; simpl; intros r Hr; [apply Hr|].
  apply IHv. intros w0. specialize (Hr (a :: w0)). exact Hr.
Qed.

(** Alternate statement matching the “prefix-removal” definition:
    ∂_u(L) = { w | u ++ w ∈ L } is regular. *)
Corollary derivative_of_regular_is_regular_concat :
  forall (L : language) (u : string),
    regular L -> regular (dlang_word_concat u L).
Proof.
  intros L u Hreg.
  destruct (derivative_preserves_regular L u Hreg) as [r Hr].
  exists r. intro w. rewrite <- dlang_equiv. apply Hr.
Qed.