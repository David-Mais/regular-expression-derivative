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