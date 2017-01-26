Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype.

(* finType *)

Check bool.
Fail Goal #| bool | == 2.

Check bool_finType.
Goal #| bool_finType | == 2.
rewrite cardT.
rewrite enumT.
rewrite unlock.
simpl Finite.mixin_enum.
simpl.
apply/eqP.
reflexivity.
Qed.

Goal [forall b : bool, (b == true) || (b == false)].
apply/forallP.
case.
simpl.
done.
simpl.
done.
Qed.

(* finType registration *)

Inductive myunit : Set :=
| mytt.

Fail Lemma myunit_enumP : Finite.axiom [:: mytt].
Set Printing All.
Fail Lemma myunit_enumP : Finite.axiom [:: mytt].
Unset Printing All.

Definition myunit_eq (a b : myunit) := true.

Lemma myunit_eqP : Equality.axiom myunit_eq.
Proof.
unfold Equality.axiom.
case.
case.
apply: (iffP idP).
done.
done.
Qed.

Definition myunit_eqMixin := EqMixin myunit_eqP.
Canonical myunit_eqType := EqType myunit myunit_eqMixin.

Check (mytt == mytt).

Lemma myunit_enumP : Finite.axiom [:: mytt].
Proof.
unfold Finite.axiom.
case.
simpl.
rewrite addn0.
reflexivity.
Qed.

Fail Definition myunit_finMixin := FinMixin myunit_enumP.
Set Printing All.
Fail Definition myunit_finMixin := FinMixin myunit_enumP.
Unset Printing All.

Lemma bool_of_myunitK : cancel (fun _ : myunit => true) (fun _ : bool => mytt).
Proof.
unfold cancel.
case.
reflexivity.
Qed.

Definition myunit_choiceMixin := CanChoiceMixin bool_of_myunitK.
Canonical myunit_choiceType := ChoiceType myunit myunit_choiceMixin.

Definition myunit_countMixin := CanCountMixin bool_of_myunitK.
Canonical myunit_countType := CountType myunit myunit_countMixin.

Definition myunit_finMixin := FinMixin myunit_enumP.
Canonical myunit_finType := FinType myunit myunit_finMixin.

Lemma card_myunit : #| myunit_finType | = 1.
Proof.
rewrite cardT.
rewrite enumT.
rewrite unlock.
simpl.
reflexivity.
Qed.

Check [forall x : myunit, x == x].
