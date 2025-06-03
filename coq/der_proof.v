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
| Star : regex -> regex.

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

Definition seq (r1 r2 : regex) : regex :=
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

Fixpoint nullable (r : regex) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Char _ => false
  | Alt r1 r2 => nullable r1 || nullable r2
  | And r1 r2 => nullable r1 && nullable r2
  | Seq r1 r2 => nullable r1 && nullable r2
  | Star _ => true
  end.

Inductive matches : regex -> string -> Prop :=
| M_Epsilon :
    matches Epsilon []
| M_Char : forall c,
    matches (Char c) [c]
| M_AltL : forall r1 r2 s,
    matches r1 s ->
    matches (Alt r1 r2) s
| M_AltR : forall r1 r2 s,
    matches r2 s ->
    matches (Alt r1 r2) s
| M_And : forall r1 r2 s,
    matches r1 s ->
    matches r2 s ->
    matches (And r1 r2) s
| M_Seq : forall r1 r2 s1 s2,
    matches r1 s1 ->
    matches r2 s2 ->
    matches (Seq r1 r2) (s1 ++ s2)
| M_Star0 : forall r,
    matches (Star r) []
| M_Star1 : forall r s1 s2,
    matches r s1 ->
    matches (Star r) s2 ->
    matches (Star r) (s1 ++ s2).

(* Forward direction proof *)
Theorem nullable_correct_forward : forall r,
  nullable r = true -> matches r [].
Proof.
  intros r H.
  induction r; simpl in H.
  - discriminate H.
  - constructor.
  - discriminate.
  - apply orb_true_iff in H as [H1 | H2].
    + apply M_AltL.
      apply IHr1. exact H1.
    + apply M_AltR.
      apply IHr2. exact H2.
  - apply andb_true_iff in H as [H1 H2].
    + apply M_And.
      apply IHr1. exact H1.
      apply IHr2. exact H2.
  - apply andb_true_iff in H as [H1 H2].
    apply M_Seq with (s1 := []) (s2 := []).
    + apply IHr1. exact H1.
    + apply IHr2. exact H2.
  - constructor.
Qed.