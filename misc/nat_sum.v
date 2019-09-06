(*
 * Proof of
     1 + 2 + ... + n = n (n + 1) / 2
 *)
Require Import Nat List Arith Omega ZArith.
From mathcomp Require Import all_ssreflect.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sum_naiive n :=
  match n with
  | 0 => 0
  | S m => n + sum_naiive m
  end.

Definition sum n := n * (n + 1) / 2.

Lemma it_is_even : forall m, Nat.Even (m + m * m).
Proof.
  move => m.
  elim m.
  - by exists 0.
  - move => n.
    case.
    move => x H.
    rewrite mulSn.
    rewrite mulnS.
    rewrite addnA.
    rewrite addnn.
    rewrite H.
    rewrite [(2 * x)%coq_nat] mul2n.
    rewrite -!mul2n.
    rewrite -mulnDr.
    exists (n.+1 + x).
    done.
Qed.

Lemma even_div_2 : forall n, n = (n + n) / 2.
Proof.
  move => n.
  apply (Nat.div_unique (n + n) 2 n 0).
  - (* Goal 0 < 2 *)
    omega.
  - rewrite [(2 * n)%coq_nat] mul2n.
    rewrite [(_ + 0)%coq_nat] addn0.
    rewrite addnn.
    done.
Qed.

Lemma even_add_even : forall n m,
  Nat.Even n -> Nat.Even m -> n / 2 + m / 2 = (n + m) / 2.
Proof.
  move => n m.
  case => x.
  rewrite [(2 * x)%coq_nat] mul2n.
  move => x2.
  case => y.
  rewrite [(2 * y)%coq_nat] mul2n.
  move => y2.
  rewrite x2.
  rewrite y2.
  rewrite -! addnn.
  replace (x + x + (y + y)) with ((x + y) + (x + y)).
  rewrite -! even_div_2.
  done.
  rewrite 2!addnA.
  rewrite -[x + x + y] addnA.
  rewrite {2} [x + y] addnC.
  rewrite !addnA.
  done.
Qed.


Theorem sum_num : forall n, sum_naiive n = sum n.
Proof.
  move => n.
  elim n => [//|m H].
  simpl.
  rewrite H.
  unfold sum.
  rewrite !addn1.
  rewrite !mulnS.
  rewrite !mulSn.
  rewrite !addnA.
  rewrite {1} [m.+1] even_div_2.
  rewrite even_add_even.
  rewrite addnA.
  done.

  rewrite addnn.
  exists (m.+1).
  rewrite -mul2n.
  done.

  by apply it_is_even.
Qed.
