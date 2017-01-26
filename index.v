Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp
Require Import div path bigop prime finset fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.

Section coset_bijection.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypothesis HG : H \subset G.

(*
Variables g h : gT.
Hypotheses (gG : g \in G) (hG : h \in G).
Check g * h : gT.
Check groupM gG hG : g * h \in G.
*)

About lcosets.

Lemma coset_disjoint (L0 L1 : {set gT}) :
  L0 \in lcosets H G -> L1 \in lcosets H G -> L0 :&: L1 != set0 -> L0 = L1.
Proof.
case/lcosetsP => g0 g0G ->{L0}.
Locate "exists2".
Print ex2.
case/lcosetsP => g1 g1G ->{L1}.
move=> Hdisj.
apply/lcoset_eqP.
case/set0Pn : Hdisj => g.
rewrite in_setI => /andP [].
rewrite !mem_lcoset => H0 H1.
rewrite -(mul1g g0).
rewrite -(mulgV g).
rewrite 2!mulgA.
rewrite -mulgA.
rewrite groupM //.
rewrite groupVl //.
by rewrite invMg invgK.
Qed.

Locate repr.

Lemma mem_repr_coset x : x \in G -> repr (x *: H) \in G.
Proof.
move=> xG.
rewrite /repr.
case: ifP => // x1.
case: pickP => /=.
  move=> x0.
  case/lcosetP => x2 Hx2 ->.
  rewrite groupM //.
  by move/subsetP : (HG); apply.
move/(_ x).
by rewrite lcoset_refl.
Qed.

Lemma repr_form x : x \in G -> repr (x *: H) *: H = x *: H.
Proof.
move=> xG.
apply coset_disjoint.
  apply/lcosetsP.
  exists (repr (x *: H)) => //.
  by apply mem_repr_coset.
  apply/lcosetsP.
  by exists x.
  apply/set0Pn => /=.
  exists (repr (x *: H)) => //.
  rewrite in_setI lcoset_refl /=.
  apply mem_repr with x => //.
  by rewrite lcoset_refl.
Qed.

Definition reprs := repr @: lcosets H G.

Lemma reprs_subset : reprs \subset G.
Proof.
apply/subsetP => g.
case/imsetP => /= gs.
case/lcosetsP => g' g'H ->{gs} ->{g}.
rewrite /repr.
case: ifP => // abs.
case: pickP => /=.
  move=> g''.
  case/lcosetP => g3 Hg3 ->.
  rewrite groupM => //.
  move/subsetP : HG; by apply.
move/(_ g').
by rewrite lcoset_refl.
Qed.

Lemma injective_coset :
  {in reprs &, injective (fun g => g *: H)}.
Proof.
(*move=> /= g g'.
rewrite {1}/reprs.
Unset Printing Notations.
Set Printing Notations.
Search _ Imset.imset.
Check (Imset.imset repr (mem (lcosets H G))).
move/imsetP.
case.
rewrite /=.
*)
move=> /= g g' /imsetP[] /= L LHG gL /imsetP[] /= K KHG g'K abs.
suff : L = K by move=> LK; rewrite LK in gL; rewrite gL g'K.
case/lcosetsP : LHG => g0 g0G g0L; subst L.
case/lcosetsP : KHG => g1 g1G g1K; subst K.
have : g *: H = g0 *: H.
  apply coset_disjoint.
  apply/lcosetsP.
  exists g => //.
  rewrite gL.
  by apply mem_repr_coset.
  apply/lcosetsP.
  by exists g0.
  apply/set0Pn; exists (repr (g0 *: H)).
  rewrite !inE -gL lcoset_refl /= gL.
  apply mem_repr with g0.
  by rewrite lcoset_refl.
move=> <-.
have : g' *: H = g1 *: H.
  apply coset_disjoint => //.
  apply/lcosetsP.
  exists g' => //.
  rewrite g'K.
  by apply mem_repr_coset.
  apply/lcosetsP.
  by exists g1.
  apply/set0Pn; exists (repr (g1 *: H)).
  rewrite inE -g'K lcoset_refl /= g'K.
  apply mem_repr with g1.
  by rewrite lcoset_refl.
by move=> <-.
Qed.

Lemma surj : (fun x => x *: H) @: reprs = lcosets H G.
Proof.
have H1 : (fun x => x *: H) @: reprs \subset lcosets H G.
  apply/subsetP => i.
  case/imsetP => g.
  case/imsetP => L HL ->{g} ->{i}.
  apply/lcosetsP.
  exists (repr L) => //.
  case/lcosetsP : HL => x xG ->.
  by apply mem_repr_coset.
have H2 : lcosets H G \subset (fun x => x *: H) @: reprs.
  apply/subsetP => i.
  case/lcosetsP => x xG ->{i}.
  apply/imsetP.
  exists (repr (x *: H)).
    rewrite /reprs.
    apply/imsetP.
    exists (x *: H) => //.
    apply/lcosetsP.
    by exists x.
  by rewrite repr_form.
apply/eqP.
by rewrite eqEsubset H1 H2.
Qed.

End coset_bijection.

Notation "#| G : H |" := #| lcosets H G |.

Section index.

Variable gT : finGroupType.
Variables G H K : {group gT}.
Hypotheses (HG : H \subset G) (KG : K \subset G) (HK : K \proper H).

Lemma index_trans : #| G : K | = (#| G : H | * #| H : K |)%nat.
Proof.
rewrite /=.
set calG := reprs G H.
have HcalG : {in calG &, injective (fun x => x *: H)}.
  by move: (injective_coset HG).
set calH := reprs H K.
have HcalH : {in calH &, injective (fun x=> x *: K)}.
  apply injective_coset.
  by move/proper_sub : (HK).
pose phi := fun gh : gT * gT => let: (g, h) := gh in (g * h) *: K.
have phi_injective : {in setX calG calH & , injective phi}.
  case => g h.
  rewrite inE /=.
  case => g' h' /andP[gG hH].
  rewrite /phi inE /= => /andP[g'G h'H] ghK.
  have H1 : (g'^-1 * g * h) *: K = h' *: K.
    move: ghK.
    (* mark *)
    move/(congr1 (fun X => g'^-1 *: X)).
    rewrite -2!lcosetM.
    by rewrite !mulgA mulVg mul1g.
  have H2 : h' *: K \proper H.
    apply/properP; split.
      apply/subsetP => x.
      case/lcosetP => x0 Hx0 ->.
      rewrite groupM //.
      by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
      move/proper_sub : HK => /subsetP; by apply.
    case/properP : HK => HK' [x xH xK].
    exists (h' * x) => //.
    rewrite groupM //.
      by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
    apply: contra xK.
    case/lcosetP => x0 x0K.
    by move/mulgI => ->.
  have H3 : (g'^-1 * g *: H) :&: H != set0.
    have H3'' : h' *: K \proper (g'^-1 * g) *: H.
      rewrite -H1.
      apply/properP; split.
        rewrite sub_lcoset.
        rewrite -lcosetM.
        rewrite mulgA.
        rewrite mulVg mul1g.
        apply/subsetP => x.
        case/lcosetP => x0 x0K ->.
        rewrite groupM //.
          by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
        by move/proper_sub : HK => /subsetP; apply.
      case/properP : HK => HK' [x xH xK].
      exists ((g'^-1 * g) * (h * x)) => //.
        rewrite mem_lcoset.
        rewrite mulgA.
        rewrite mulVg.
        rewrite mul1g groupM //.
        by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
      rewrite mem_lcoset.
      rewrite -(mulgA g'^-1 g (h * x)).
      rewrite (mulgA g h x).
      rewrite (mulgA g'^-1 (g * h) x).
      rewrite (mulgA g'^-1 g h).
      rewrite mulgA.
      by rewrite mulVg mul1g.
    (* use H2 to conclude *)
    apply/set0Pn.
    case/properP : HK => HK' [x xH xK].
    exists h'.
    rewrite in_setI.
    apply/andP; split.
      move/proper_sub/subsetP : H3''.
      apply.
      rewrite mem_lcoset.
      by rewrite mulVg group1.
    by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
  have H4 : (g'^-1 * g) *: H = H.
    case/set0Pn : H3 => x.
    rewrite in_setI.
    case/andP.
    case/lcosetP => x0 Hx0 -> Htmp.
    rewrite lcoset_id //.
    rewrite -(mulg1 g).
    rewrite -(mulgV x0).
    rewrite !mulgA.
    rewrite groupM //.
    by rewrite groupVl // invgK.
  have H5 : g *: H = g' *: H.
    rewrite -{2}H4.
    rewrite -lcosetM.
    by rewrite mulgA mulgV mul1g.
  have H6 : g = g'.
    by apply HcalG.
  have H7 : h *: K = h' *: K.
    subst g'.
    by rewrite mulVg mul1g in H1.
  have H8 : h = h'.
    by apply HcalH.
  by rewrite H6 H8.
have surj1 : (fun x => x *: H) @: calG = lcosets H G.
  by apply surj.
have surj2 : (fun x => x *: K) @: calH = lcosets K H.
  apply surj.
  by move/proper_sub : (HK); apply.
have surj3 : phi @: (setX calG calH) = lcosets K G.
  apply/setP => /= i.
  apply/idP/idP.
    case/imsetP => /=; case=> [x1 x2].
    rewrite !inE /= => /andP[Hx1 Hx2] ->{i}.
    apply/lcosetsP.
    exists (x1 * x2) => //.
    rewrite groupM //.
    by move : (HG) => /reprs_subset /subsetP; apply.
    move/subsetP : HG; apply.
    move : x2 Hx2.
    apply/subsetP.
    by apply/reprs_subset/proper_sub.
  case/lcosetsP => l lG ->{i}.
  apply/imsetP => /=.
  have [g [gcalG Hg]] : exists g, g \in calG /\ g *: H = l *: H.
    exists (repr (l *: H)).
    split.
      apply/imsetP.
      exists (l *: H) => //.
      apply/lcosetsP.
      by exists l.
    by rewrite (repr_form HG).
  have H1 : (g^-1 * l) *: H = H.
    move/(congr1 (fun x => g^-1 *: x)) in Hg.
    by rewrite -!lcosetM mulVg lcoset1 in Hg.
  have H2 : g^-1 * l \in H.
    rewrite -H1.
    by rewrite lcoset_refl.
  have [h [hcalH Hh]] : exists h, h \in calH /\ (g^-1 * l) *: K = h *: K.
    exists (repr ((g^-1 * l) *: K)).
    split.
      apply/imsetP.
      exists ((g^-1 * l) *: K) => //.
      apply/lcosetsP.
      by exists (g^-1 * l) => //.
    rewrite (repr_form KG) //.
    rewrite groupM //.
    rewrite groupVl // invgK //.
    by move: (reprs_subset HG) => /subsetP; apply.
  exists (g, h).
    by rewrite in_setX gcalG.
  move/(congr1 (fun x => g *: x)) in Hh.
  rewrite -!lcosetM in Hh.
  rewrite /phi.
  rewrite -Hh.
  by rewrite mulgA mulgV mul1g.
rewrite -surj3 -surj1 -surj2.
rewrite (card_in_imset phi_injective).
rewrite cardsX.
rewrite (card_in_imset HcalG).
by rewrite (card_in_imset HcalH).
Qed.

End index.

Section lagrange.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypotheses (HG : H \subset G).

Lemma H3 g : g *: (1%G : {group gT}) = [set g].
Proof.
apply/setP => j.
rewrite !inE.
apply/idP/idP => //.
  case/lcosetP => x.
  rewrite !inE => /eqP ->.
  by rewrite mulg1 => /eqP.
move/eqP => ->.
apply/lcosetP.
 exists 1 => //.
by rewrite mulg1.
Qed.

Lemma lcosets1 (K : {group gT}) : lcosets 1%G K = (set1) @: K.
Proof.
apply/setP => i.
apply/idP/idP.
  case/lcosetsP => g gK ->{i}.
  apply/imsetP.
  exists g => //.
  by apply H3.
case/imsetP => g gK ->{i}.
apply/lcosetsP.
exists g => //.
by rewrite H3.
Qed.

Theorem Lagrange : #| G | = (#| H | * #| G : H |)%nat.
Proof.
have [H1|H1] := boolP (1%G \proper H); last first.
  suff -> : H = 1%G.
    rewrite cards1 mul1n lcosets1 // card_imset //.
    exact: set1_inj.
  apply/trivGP.
  rewrite proper1G negbK in H1.
  by rewrite (eqP H1).
have G1 : 1%G \subset G.
  apply/subsetP => h.
  by rewrite inE => /eqP ->.
move: (index_trans HG G1 H1).
rewrite lcosets1.
rewrite card_imset; last first.
  exact: set1_inj.
move=> ->.
rewrite mulnC lcosets1 card_imset //.
  exact: set1_inj.
Qed.

End lagrange.
