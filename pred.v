(** * %V\'erification% de programmes %\coq% *)

(** ** La fonction %pr\'ed\'ecesseur%

 *)

Print nat.
Definition prec (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

Compute prec 5.
Compute prec 0.

Recursive Extraction prec.

(** %\`A% utiliser avec %pr\'ecaution% puisqu'elle retourne $0$ pour $0$. *)


(** ** La fonction %pr\'ed\'ecesseur% partielle

  Prend en argument une preuve que l'%entr\'ee% est strictement positive.

*)

Print False.
Definition false_nat (abs : False) : nat :=
  match abs with end.

Require Import Arith.
Check lt_irrefl.

Axiom faux : O < O.
Check (Nat.lt_irrefl _ faux).
Check (false_nat (Nat.lt_irrefl _ faux)).

Definition pprec (n : nat) : 0 < n -> nat :=
  match n with
  | O => fun H => false_nat (Nat.lt_irrefl _ H)
  | S m => fun _ => m
  end.

Recursive Extraction pprec.

(** ** Construire des preuves d'%in\'egalit\'es%
*)

Print le.
Check le_S _ _ (le_n 1).

Fixpoint spos (n : nat) : 1 <= S n :=
  match n with
  | O => le_n 1
  | S m => le_S _ _ (spos m)
  end.

Compute pprec 5 (spos _).

(** ** Construire des preuves d'%\'egalit\'es%
*)

Print eq.
Check (eq 0 1).
Check (@eq _ 0 1).
Check eq_refl 0.
Check (@eq_refl _ 0). 
Check eq_refl (2 + 2) : 4 = 2 + 2.

About Nat.leb.
Print Nat.ltb.
About Nat.ltb_lt.

Definition pprecb (n : nat) : Nat.ltb 0 n = true -> nat :=
  match n with
  | O => fun H => false_nat
    (Nat.lt_irrefl _ (proj1 (Nat.ltb_lt _ _) H))
  | S m => fun _ => m
  end.

Compute pprecb 5 eq_refl.
Fail Compute pprecb 0 eq_refl.

Recursive Extraction pprecb.

(** ** Fonction %pr\'ed\'ecesseur% partielle %compl\`etement% %sp\'ecifi\'ee%

  Tout est dans le type.

  *)

(** *** Progammation interactive

 *)

Print sig.
Print proj1_sig.
Check (exist (fun x => x = O) 0 eq_refl) : {x : nat | x = 0}.

Definition pprec_interactif (n : nat) :
  0 < n -> {m | n = S m}.
destruct n as [|m].
- intros abs.
  generalize (Nat.lt_irrefl _ abs).
  destruct 1.
- intros _.
  apply (exist _ m).
  apply eq_refl.
Defined.

Print pprec_interactif.

Recursive Extraction pprec_interactif.

(** *** Progammation avec l'extension %\lstinline!Program!%

 *)

Program Definition pre_auto (n : nat) : 0 < n -> {m | n = S m} :=
  match n with
  | O => fun H => False_rect _ (Nat.lt_irrefl _ H)
  | S m => fun _ => exist (fun x => n = S x) m _
  end.

Obligation Tactic := idtac.
Program Definition pre_manual (n : nat) : 0 < n -> {m | n = S m} :=
  match n with
  | O => fun H => False_rect _ (Nat.lt_irrefl _ H)
  | S m => fun _ => exist (fun x => n = S x) m _
  end.
Next Obligation.
intros n m mn _.
simpl.
rewrite mn.
apply eq_refl.
Qed.
Next Obligation.
intros n m mn Om.
simpl.
apply eq_refl.
Qed.

Print pre_auto.
Print pre_manual.

(** *** Progammation directe

 *)

About eq_ind.

Definition pre (n : nat) : 0 < n -> {m | n = S m} :=
  (match n as n' return n = n' -> _ with
  | O => fun _ H => False_rect _ (Nat.lt_irrefl _ H)
  | S m => fun Heq _ => exist (fun x => n = S x) m Heq
  end) eq_refl.

Print pre.

Compute proj1_sig (pre 5 (spos _)).
