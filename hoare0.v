(** * %V\'erification% de programmes avec la logique de Hoare *)

(** ** Syntaxe des expressions %arithm\'etiques% et %bool\'eennes%

*)

Definition var := nat.

Inductive exp :=
| exp_var : var -> exp
| cst : nat -> exp
| mul : exp -> exp -> exp
| sub : exp -> exp -> exp.

Inductive bexp :=
| equa : exp -> exp -> bexp
| neg : bexp -> bexp.

(** ** Un langage %imp\'eratif% minimal
*)

Inductive cmd : Type :=
| assign : var -> exp -> cmd
| seq : cmd -> cmd -> cmd
| while : bexp -> cmd -> cmd.

(** ** %S\'emantique% des expressions *)

(** %\'Etat% d'un programme: *)

Definition state := var -> nat.

Definition sample_state : state :=
  fun x =>
    match x with
    | O => 4
    | 1 => 5
    | _ => O
    end.

Require Import Arith.

Definition upd (v : var) (a : nat) (s : state) : state :=
  fun x => match Nat.eq_dec x v with
           | left _ (* x = y *) => a
           | right _ => s x
           end.

(** %\'Evaluation% des expressions: *)

Fixpoint eval e s :=
  match e with
  | exp_var v => s v
  | cst n => n
  | mul v1 v2 => eval v1 s * eval v2 s
  | sub v1 v2 => eval v1 s - eval v2 s
  end.

Fixpoint beval b s :=
  match b with
    | equa e1 e2 => eval e1 s = eval e2 s
    | neg b => ~ beval b s
  end.

(** Exemple d'expression: *)

Definition ret : var := O.
Definition x : var := 1.

Compute eval (mul (exp_var ret) (exp_var x)) sample_state.

(* begin hide *)
Lemma eval_upd_same str v s : eval (exp_var str) (upd str v s) = v.
Proof.
simpl.
unfold upd.
destruct Nat.eq_dec.
apply eq_refl.
tauto.
Qed.

Lemma eval_upd_diff str str' v s : str <> str' -> eval (exp_var str) (upd str' v s) = eval (exp_var str) s.
Proof.
intros H.
simpl.
unfold upd.
destruct Nat.eq_dec.
  tauto.
apply eq_refl.
Qed.
(* end hide*)

(** ** R%\'e%presentation de la logique de Hoare *)

(** %D\'efinition% des %pr\'e/post%-conditions: *)

Definition assert := state -> Prop.

Definition imp (P Q : assert) := forall s, P s -> Q s.

(** Les %r\`egles% d'%inf\'erence%: *)

Inductive hoare : assert -> cmd -> assert -> Prop :=
| hoare_assign : forall (Q : assert) v e,
  hoare (fun s => Q (upd v (eval e s) s)) (assign v e) Q
| hoare_seq : forall Q P R c d,
  hoare P c Q -> hoare Q d R ->
  hoare P (seq c d) R
| hoare_conseq : forall (P' Q' P Q : assert) c,
  imp P P' -> imp Q' Q -> hoare P' c Q' ->
  hoare P c Q
| hoare_while : forall P b c,
  hoare (fun s => P s /\ beval b s) c P ->
  hoare P (while b c) (fun s => P s /\ ~ (beval b s)).

(* begin hide*)
Lemma hoare_stren : forall (P' P Q : assert) c,
  imp P P' -> hoare P' c Q -> hoare P c Q.
Proof.
intros P' P Q c PP' H.
apply (hoare_conseq P' Q).
auto.
unfold imp.
auto.
auto.
Qed.
(* end hide *)

(* begin hide *)
Definition facto (x ret : var) :=
  while (neg (equa (exp_var x) (cst O)))
    (seq
       (assign ret (mul (exp_var ret) (exp_var x)))
       (assign x (sub (exp_var x) (cst 1)))).

Require Import Omega.
Require Import Factorial.

Lemma fact_fact n : 1 <= n -> fact (n - 1) * n = fact n.
Proof.
destruct n as [|n].
omega.
intros _.
simpl.
rewrite Nat.sub_0_r.
rewrite Nat.mul_succ_r.
rewrite Nat.mul_comm.
omega.
Qed.
(* end hide *)