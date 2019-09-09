(*
 * その7: https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/class/cal/handout7.pdf
 * 帰納命題
 *)

Require Import Arith List Omega ZArith.
From mathcomp Require Import all_ssreflect.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
帰納型の宣言
*)
Inductive ev : nat -> Prop :=
| ev_O : ev 0
| ev_SS n (H : ev n) : ev n.+2.

Check (ev 0).
Check ev_O.  (* ev 0 *)
Check (ev_SS ev_O).  (* ev 2 *)
Check (ev_SS (ev_SS ev_O)).  (* ev 4 *)

(*
帰納構造に関する証明
*)

Theorem four_is_even : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  by apply ev_O.
Qed.

(*
逆転の定理
*)
Theorem ev_inversion :
  forall n, ev n -> n = 0 \/ (exists m, n = m.+2 /\ ev m).
Proof.
  intros n Hn.
  destruct Hn as [|m Hm].
  - by left.
  - right.
    exists m.
    done.
Qed.

(*
inversion タクティクス
*)
Theorem evSS_ev : forall n, ev n.+2 -> ev n.
Proof.
  intros n E.
  inversion E as [|m H1 H2].
  exact.
Qed.

Theorem evSSSS_ev : forall n, ev n.+4 -> ev n.
Proof.
  intros n E.
  inversion E as [|m H1 H2].
  inversion H1 as [|k H3 H4].
  exact.
Qed.

Theorem inversion_ex1 : forall n m o : nat, [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H. (* works as injection *)
  done.
Qed.

Theorem inversion_ex2 : forall n : nat, n.+1 = 0 -> 2 + 2 = 5.
Proof.
  intros n H.
  inversion H.  (* works as discriminate *)
Qed.

Theorem inversion_ex_S_injective : forall n m, S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  exact.
Qed.

(*
  ev の構造に関する帰納法
 *)
Lemma even_is_double_of_something : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E.
  - by exists 0.
  - destruct IHE.
    exists (x.+1).
    rewrite -muln2.
    rewrite mulSn.
    rewrite muln2.
    rewrite -H.
    done.
Qed.
