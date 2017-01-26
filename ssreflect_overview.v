(* 1. is_true coercion *)
Locate le.
Check le.

Goal 1 <= 5.
auto.
Show Proof.
Qed.

Require Import Nat.
Locate leb.
Check leb.

Goal 1 <=? 5 = true.
simpl.
reflexivity.
Show Proof.
Qed.

Fail Goal 1 <=? 5.

Coercion myis_true (b : bool) : Prop := b = true.

Goal 1 <=? 5.
Set Printing Coercions.
Unset Printing Coercions.
Abort.

Reset myis_true.
Fail Check myis_true.

From mathcomp Require Import ssreflect ssrfun ssrbool.

Print is_true.

(* 2. view mechanism *)

Locate leb.
Require Import Arith. (* more lemmas about leb *)

Lemma leP_equiv a b : le a b <-> leb a b.
Proof.
split.
apply leb_correct.
apply leb_complete.
Qed.

Goal 1 <= 5.
apply/leP_equiv.
simpl.
reflexivity.
Qed.

Goal 1 <= 5.
apply (iffRL (leP_equiv 1 5)).
simpl.
reflexivity.
Qed.

(* 3. reflect predicate *)

Locate reflect.
Print mathcomp.ssreflect.ssrbool.reflect.

Lemma leP a b : reflect (a <= b) (a <=? b). 
Proof.
apply: (iffP idP).
apply leb_complete.
apply leb_correct.
Qed.

Goal 1 <= 5.
apply/leP.
simpl.
reflexivity.
Qed.

Goal 1 <= 5.
apply (elimT (leP 1 5)).
simpl.
reflexivity.
Qed.

(* eqtype registration *)

Print Nat.eqb.

Lemma NateqbP (a b : nat) : reflect (a = b) (Nat.eqb a b).
Proof.
apply: (iffP idP).
apply beq_nat_true.
move ->.
apply Nat.eqb_refl.
Qed.

Goal 1 = 1 -> Nat.eqb 1 1.
move/NateqbP.
Abort.

Require Import eqtype.

Check (true == false).
Set Printing All.
Check (true == false).
Unset Printing All.
Fail Check (0 == 1).

Lemma equality_axiom_NateqbP : Equality.axiom Nat.eqb.
Proof.
exact NateqbP.
Qed.

Definition nat_eqMixin := EqMixin equality_axiom_NateqbP.

Fail Check (0 == 1).
Notation "x === y" := (Equality.op nat_eqMixin x y) (at level 70).
Check (0 === 1).
Goal 0 === 0.
simpl.
reflexivity.
Qed.

Notation "x ==== y" := (Equality.op _ x y) (at level 70).
Check (0 ==== 1).
Fail Goal (0 ==== 1).

Check (nat_eqMixin : Equality.mixin_of nat).

Canonical nat_eqType := EqType nat nat_eqMixin.

Unset Printing Notations.
Check (0 == 1).
Set Printing Notations.

Goal 1 = 1 -> 1 == 1.
move/NateqbP.
Undo.
move/eqP.
Abort.

Goal forall (a b c : nat), a == b -> b == c -> a == c.
move=> a b c ab bc.
Fail rewrite ab.
rewrite (eqP ab).
Undo.
move/eqP : ab ->.
assumption.
Qed.
