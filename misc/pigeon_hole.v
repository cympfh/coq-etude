(* From mathcomp Require Import ssreflect ssrfun eqtype *)
Require Import Nat List Arith Omega ZArith.
From mathcomp Require Import all_ssreflect.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma lt_SnSm : forall n m, S n < S m -> n < m.
Proof.
  done.
Qed.

Lemma gt_Snm : forall n m, S n < m -> n < m.
Proof.
  move => n m.
  have: n < n.+1 by rewrite //.
  apply ltn_trans.
Qed.

Fixpoint summation (xs : list nat) :=
  match xs with
  | nil => 0
  | x :: xs' => x + summation xs'
  end.

Lemma summation_0 : forall xs,
  size (0 :: xs) < summation (0 :: xs) -> size xs < summation xs.
Proof.
  simpl.
  move => xs.
  apply gt_Snm.
Qed.

Lemma summation_1 : forall xs,
  size (1 :: xs) < summation (1 :: xs) -> size xs < summation xs.
Proof.
  simpl.
  move => xs.
  rewrite add1n.
  apply lt_SnSm.
Qed.

Theorem Pigeon_Hole : forall (xs : list nat),
  size xs < summation xs -> exists x, In x xs /\ x >= 2.
Proof.
  elim => [//|y ys H].
  case y.
  - (* y = 0 *)
    move/summation_0.
    move/H.
    case.
    move => x.
    case.
    move => I J.
    exists x.
    split.
    - simpl.
      by right.
    - exact.
  - (* y = z + 1 *)
    move => z.
    case z.
    - (* y = 1 *)
      move/summation_1.
      move/H.
      case.
      move => x.
      case.
      move => I J.
      exists x.
      split.
      - simpl.
        by right.
      - exact.
    - (* y = n+2 (y >= 2) *)
      move => n.
      exists (n.+2).
      split.
      - by simpl; left.
      - done.
Qed.
