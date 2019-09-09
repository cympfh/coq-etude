(*
 * その6: https://www.fos.kuis.kyoto-u.ac.jp/~igarashi/class/cal/handout6.pdf
 * 論理演算の練習
 *)

Require Import Arith List Omega ZArith.
From mathcomp Require Import all_ssreflect.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
論理演算の練習
*)

Theorem ex_falso : forall P: Prop, False -> P.
Proof.
  intros P falso.
  destruct falso.
Qed.

Theorem double_neg : forall (P:Prop), P -> ~ ~P.
Proof.
  intros P HP.
  unfold not.
  intro HnotP.
  apply (HnotP HP).
Qed.

Theorem iff_sym : forall P Q: Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [PQ QP].
  split.
  - exact.
  - exact.
Qed.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n m.
  split.
  - (* => *)
    case n as [|n'].
    + (* when n = 0 *)
      by left.
    + (* when n = S n' *)
      case m as [|m'].
      * (* when m = 0 *)
        by right.
      * (* when m = S m' *)
        discriminate.
  - (* <= *)
    case.
    + intro n_is_0.
      rewrite n_is_0.
      done.
    + intro m_is_0.
      rewrite m_is_0.
      done.
Qed.

Lemma mult_0_3 : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite !mult_0.
  by rewrite or_assoc.
Qed.

(*
exists の練習
*)

Theorem exists_ex2 : forall n,
  (exists m, n = 4 + m) -> (exists k, n = 2 + k).
Proof.
  intros n.
  intros H.
  destruct H.
  exists (2 + x).
  rewrite H.
  done.
Qed.

Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.

Example function_equality_ex : (fun x => x + 1) = (fun x => 1 + x).
Proof.
  apply functional_extensionality.
  intro x.
  rewrite [x+1] addnC.
  done.
Qed.

(*
証明に用いた公理の確認
*)
Print Assumptions function_equality_ex.

(*
古典論理の話
*)

(* 排中律 *)
Definition ext_mid := forall P, P \/ ~P.

(*
 を仮定すると以下が成り立つ
 *)

Theorem Peirce_law : forall P Q : Prop,
  ext_mid -> ((P -> Q) -> P) -> P.
Proof.
  unfold ext_mid.
  intros P Q ExtMidLaw.
  move: (ExtMidLaw P).
  case.
  - (* when P *)
    done.
  - (* when not P *)
    move => HnotP H.
    apply H.
    move/HnotP.
    done.
Qed.

Theorem ClassicTheorem : ext_mid -> forall (P Q : Prop), (P -> Q) -> ~P \/ Q.
Proof.
  unfold ext_mid.
  intros ExtMidLaw P Q HPQ.
  move: (ExtMidLaw P).
  case.
  - (* when P *)
    move/HPQ.
    by right.
  - (* when not P *)
    by left.
Qed.
