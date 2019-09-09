From mathcomp Require Import all_ssreflect.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Check Equality.axiom.
Check Zeq_bool.
Check rel.

Lemma Zeq_boolP : Equality.axiom Zeq_bool.
Proof.
    move => x y.
    by apply: (iffP idP); rewrite Zeq_is_eq_bool.
Qed.

Restart.
Show.
Undo.

