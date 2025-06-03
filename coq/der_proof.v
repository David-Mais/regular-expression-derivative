Require Import Ascii.

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
  | Empty, _r | _r, Empty => r1
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
  | Epsilon, _r | _r, Epsilon => _r
  | _, _ => Seq r1 r2
  end.

Definition star (r1 : regex) : regex :=
  match r1 with
  | Empty | Epsilon => Epsilon
  | Star _r => Star _r
  | _ => Star r1
  end.