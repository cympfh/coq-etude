(*
 * その5: https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/class/cal/handout5.pdf
 * タクティクスの練習
 *)

Require Import Arith List Omega ZArith.
From mathcomp Require Import all_ssreflect.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  congruence.
Qed.

(*
 * ただの apply では m が推測できないが with でヒントを与えることが出来る
 *)

Example trans_eq_example :
  forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m := [c;d]).
  - exact.
  - exact.
Qed.

(*
 * 帰納的定義では、イコールは構築の仕方から自明なもの
 *)

Theorem S_injective : forall n m,
  S n = S m -> n = m.
Proof.
  intros.
  assert (H2 : n = (n.+1).-1). {
    by simpl.
  }
  rewrite H2.
  rewrite H.
  by simpl.
Qed.

(*
 * これをやってくれる injection というタクティクがある
 *)

Theorem S_injective' : forall n m,
  S n = S m -> n = m.
Proof.
  intros.
  injection H.
  apply.
Qed.

Theorem injection_ex1 : forall n m o : nat,
  [n;m] = [o;o] -> [n] = [m].
Proof.
  intros.
  injection H.
  intros.
  rewrite H0.
  rewrite H1.
  trivial.
Qed.

Theorem injection_ex2 : forall n m : nat,
  [n] = [m] -> n = m.
Proof.
  intros n m.
  intros H.
  injection H as Hnm.
  exact.
Qed.

Theorem injection_ex2' : forall n m : nat,
  Some n = Some m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  exact.
Qed.

(*
* 同様にイコールでないことも構築の仕方から自明に分かる
* それを即座に使うのが discriminate
*)

Theorem eqb_0_1 : forall n, 0 = n -> n = 0.
Proof.
  intros [|m].
  - done.
  - discriminate.
Qed.

Theorem explosion_ex1 : forall n, n.+1 = 0 -> 0 = 100.
Proof.
  discriminate.
Qed.

(*
* ちなみに injection の逆は定理である
*)

Check f_equal.

Theorem f_equal' : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros.
  rewrite H.
  trivial.
Qed.

(*
自然数の二倍にする関数 double が injective であることを
数学的帰納法で示す練習
*)

Check double.
Compute (double 3). (* 6 *)

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  induction n.
  - (* when n = 0; m must be 0 *)
    case.
    + (* when m = 0; ok *)
      done.
    + (* when m = _.+1; ng *)
      discriminate.
  - (* when n = _.+1 *)
    induction m.
    + (* when m = 0; ng *)
      discriminate.
      rewrite -! muln2.
      rewrite !mulSn.
      rewrite !muln2.
      intro SS.
      injection SS.
      move/IHn.
      apply f_equal.
Qed.

(*
量化に気をつけないと失敗する
*)

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  induction n as [|n'].
  - (* when n = 0 *)
    intro eq.
    destruct m.
    + done.
    + discriminate.
  - (* when n = S n' *)
    intro eq.
    destruct m as [|m'].
    + (* when m = 0 *)
      discriminate.
    + (* when m = S m' *)
Abort.

(*
generalize dependent タクティクは全称量化を導入できる
move: とか revert と同じ？
*)

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  (*
  move: n.
  revert n.
  *)
  induction m.
Abort.

(*
条件式の場合分け
*)

Definition silly_fun (n : nat) : bool :=
  if n == 3 then false
  else if n == 5 then false
  else false.

Theorem silly_fun_returns_false : forall n, silly_fun n = false.
Proof.
  intro n.
  unfold silly_fun.
  - case (n == 3).
    done.
  - case (n == 5).
    done.
  - (* else *)
    done.
Qed.

Check odd.
Compute (odd 3).
Compute (odd 4).

Definition silly_fun1 (n : nat) : bool :=
  if n == 3 then true
  else if n == 5 then true
  else false.

Theorem silly_fun1_is_true : forall n : nat,
  silly_fun1 n = true -> odd n = true.
Proof.
  intro n.
  unfold silly_fun1.
  - case (n == 3) eqn:n_is_3.
    move/eqP in n_is_3.  (* _ == _ -> _ = _ *)
    rewrite n_is_3.
    done.
  - case (n == 5) eqn:n_is_5.
    move/eqP in n_is_5.
    rewrite n_is_5.
    done.
  - discriminate.
Qed.
