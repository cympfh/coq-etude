(* 集合論 *)

Require Import Arith List Logic Bool.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 集合とは所属を判定する述語 *)
Definition Set' (M: Type) := M -> Prop.
Definition belong {M: Type} (A: Set' M) (x: M) : Prop := A x.
Notation "x <- A" := (belong A x) (at level 11).

Definition EmptySet {M: Type} : Set' M := fun _ => False.
Definition Universe {M: Type} : Set' M := fun _ => True.

(* 包含関係 *)
Definition subset {M: Type} (A: Set' M) (B: Set' M) : Prop :=
    forall x: M, x <- A -> x <- B.
Notation "A <# B" := (subset A B) (at level 11).

Section subset_lemmas.
    Variable M: Type.

    Lemma AnyIsSubOfUniverse (A: Set' M) : A <# Universe.
    Proof.
        (* 定義より明らか *)
        rewrite /Universe /subset /belong.
        done.
    Qed.

    Lemma EmptyIsSubOfAny (A: Set' M) : EmptySet <# A.
    Proof.
        rewrite /EmptySet /subset /belong.
        done.
    Qed.

    Lemma SubReflection (A: Set' M) : A <# A.
    Proof.
        rewrite /subset /belong.
        done.
    Qed.

    (* 包含関係は遷移的 *)
    Lemma SubTransitivity (A B C: Set' M) : A <# B /\ B <# C -> A <# C.
    Proof.
        case.
        rewrite /subset => H I x.
        move/ (H x).
        by move/ (I x).
    Qed.

End subset_lemmas.

(* 同値関係 *)

Definition SetEqual {M: Type} (A: Set' M) (B: Set' M) : Prop :=
    A <# B /\ B <# A.

(* イコールなら SetEqual なのは自然に従う *)
Theorem SetEqualityDestruction {M: Type} : forall A B: Set' M,
    A = B -> SetEqual A B.
Proof.
    move => A B eq.
    rewrite /SetEqual.
    rewrite -eq.
    split.
    - done.
    - done.
Qed.

(* 逆は従わないので公理化する *)
Axiom SetEqualityAxiom : forall {M: Type} (A B: Set' M),
    SetEqual A B -> A = B.

Section eq_lemmas.
    Variable M: Type.

    Lemma SetEqReflection (A: Set' M) : M = M.
    Proof.
        done.
    Qed.

    Lemma SetEqSym (A B: Set' M) : A = B -> B = A.
    Proof.
        done.
    Qed.

End eq_lemmas.

(* 集合演算 *)

Definition comp {M: Type} (A: Set' M) : Set' M :=
    fun x => ~(A x).

Definition cup {M: Type} (A B: Set' M) : Set' M :=
    fun x => (x <- A) \/ (x <- B).

Definition cap {M: Type} (A B: Set' M) : Set' M :=
    fun x => (x <- A) /\ (x <- B).

Notation "A \cup B" := (cup A B) (at level 11).
Notation "A \cap B" := (cap A B) (at level 11).

Section ops_lemmas.
    Variable M: Type.

    Lemma compEmptyIsUniverse : @comp M EmptySet = Universe.
    Proof.
        apply SetEqualityAxiom.
        rewrite /SetEqual /subset /belong /comp /EmptySet /Universe.
        split.
        - done.
        - rewrite /not.
          done.
    Qed.

    Lemma compUniverseIsEmpty : @comp M Universe = EmptySet.
    Proof.
        apply SetEqualityAxiom.
        rewrite /SetEqual /subset /belong /comp /EmptySet /Universe.
        split.
        - done.
        - done.
    Qed.

    (* 排中律を仮定すれば次が示せる *)
    Hypothesis HypothesisOfExcludedMiddle :
        forall A: Set' M, forall x: M, (x <- A) \/ ~(x <- A).

    Lemma cc_cancel : forall A: Set' M, comp (comp A) = A.
    Proof.
        move => A.
        apply SetEqualityAxiom.
        rewrite /SetEqual /subset.
        split.
        - move => x.
          move: (HypothesisOfExcludedMiddle A x).
          case.
          - done.
          - by rewrite /comp.
        - move => x.
          move: (HypothesisOfExcludedMiddle (comp A) x).
          case.
          - by rewrite /comp.
          - by rewrite /comp.
    Qed.

    (* 排中律の削除 *)
    Reset HypothesisOfExcludedMiddle.

    (* 和演算の結合性 *)
    Lemma cupAssoc : forall A B C: Set' M,
        (A \cup B) \cup C = A \cup (B \cup C).
    Proof.
        move => A B C.
        apply SetEqualityAxiom.
        rewrite /SetEqual /subset /cup /belong.
        split.
        - move => x.
          by rewrite or_assoc.
        - move => x.
          by rewrite or_assoc.
    Qed.

    (* 積集合も全く同様の性質 *)
    Lemma capAssoc : forall A B C: Set' M,
        (A \cap B) \cap C = A \cap (B \cap C).
    Proof.
        move => A B C.
        apply SetEqualityAxiom.
        rewrite /SetEqual /subset /cap /belong.
        split.
        - move => x.
          by rewrite and_assoc.
        - move => x.
          by rewrite and_assoc.
    Qed.

End ops_lemmas.

(* 関数の定義 *)

Definition Function {M N: Type} (A: Set' M) (B: Set' N) (f: M -> N) :=
    forall x: M, x <- A -> (f x) <- B.

Definition Composition {M N K: Type} (f: M -> N) (g: N -> K) : M -> K :=
    fun x => g (f x).

Notation "f \colon A \to B" := (Function A B f) (at level 11).
Notation "g \circ f" := (Composition f g) (at level 11).

Definition Image {M N: Type} (f: M -> N) {A: Set' M} {B : Set' N} (_ : f \colon A \to B)
    : Set' N :=
    fun (y: N) => exists (x: M), x <- A /\ f x = y.

Definition Injective {M N: Type} {f: M -> N} {A: Set' M} {B: Set' N} (_ : f \colon A \to B) :=
    forall (x y: M), (x <- A) -> (y <- A) -> (f x = f y) -> x = y.

Definition Surjective {M N: Type} {f: M -> N} {A: Set' M} {B: Set' N} (_ : f \colon A \to B) :=
    forall (y: N), (y <- B) -> exists (x: M), (x <- A) /\ f x = y.

Definition Bijective {M N: Type} {f: M -> N} {A: Set' M} {B: Set' N} (P : f \colon A \to B) :=
    (@Injective M N f A B P) /\ (@Surjective M N f A B P).

Section function_lemmas.

    Variable M N K: Type.
    Variable f : N -> K.
    Variable g : M -> N.
    Variable A : Set' M.
    Variable B : Set' N.
    Variable C : Set' K.
    Hypothesis Pf : f \colon B \to C.
    Hypothesis Pg : g \colon A \to B.

    (* 単射どうしの合成は単射 *)
    Lemma trans_inj (Pfg: (f \circ g) \colon A \to C) :
        Injective Pf -> Injective Pg -> Injective Pfg.
    Proof.
        rewrite /Injective.
        move => H I x y xA yA J.
        apply: (I x y xA yA).
        apply: (H (g x) (g y)).
        by apply: Pg.
        by apply: Pg.
        by apply J.
    Qed.

    (* 関数と関数を合成したものは関数 *)
    Lemma compose_is_function : (f \circ g) \colon A \to C.
    Proof.
        rewrite /Composition.
        rewrite /Function.
        move => x xA.
        cut ((g x) <- B).
        - move => gxB.
          by apply: Pf.
        - by apply: Pg.
    Qed.

End function_lemmas.

Show.
Undo.
Restart.
