(** Inversion and uniqueness for the internal relativization computation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent NumericalTraces FreshNames
  SourceRelativizationRules SourceRelativization.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition sr_source_atom (equality:bool) := if equality then SFEqual else SFMember.

Theorem source_relativization_cases M d f v : source_relativization M d f v ->
  sr_leaf M f v \/
  (exists universal a w,sf_relation M (sr_source_quantifier universal) a (zeroM M) f /\
    source_relativization M d a w /\ sr_quantifier M universal d w v) \/
  (exists h a b x y,sf_binary h /\ sf_relation M h a b f /\
    source_relativization M d a x /\ source_relativization M d b y /\ sf_relation M h x y v).
Proof.
  intros [r [HR HD]]. destruct (trace_derives_inv M source_relativization_rules r HD)
    as [HB|[[p [HP HU]]|[p [q [HP [HQ HB]]]]]].
  - apply sr_rule_base in HB. destruct HB as [d' [f' [v' [HR' HL]]]].
    destruct (sr_record_injective M d f v d' f' v' r HR HR') as [Ed [Ef Ev]].
    subst d' f' v'. now left.
  - apply sr_rule_unary in HU. destruct HU as [d' [f' [v' [a [w [HR' [HChild HH]]]]]]].
    destruct (sr_record_injective M d f v d' f' v' r HR HR') as [Ed [Ef Ev]].
    subst d' f' v'. right;left. destruct HH as [[HF HV]|[HF HV]].
    + exists true,a,w. split;[exact HF|]. split;[exists p;auto|exact HV].
    + exists false,a,w. split;[exact HF|]. split;[exists p;auto|exact HV].
  - apply sr_rule_binary in HB. destruct HB as [d' [f' [v' [a [b [x [y [HR' [HX [HY HH]]]]]]]]]].
    destruct (sr_record_injective M d f v d' f' v' r HR HR') as [Ed [Ef Ev]].
    subst d' f' v'. right;right.
    destruct HH as [[HF HV]|[[HF HV]|[HF HV]]].
    + exists SFAnd,a,b,x,y. split;[now left|]. split;[exact HF|].
      split;[exists p;auto|]. split;[exists q;auto|exact HV].
    + exists SFOr,a,b,x,y. split;[right;now left|]. split;[exact HF|].
      split;[exists p;auto|]. split;[exists q;auto|exact HV].
    + exists SFImpl,a,b,x,y. split;[right;now right|]. split;[exact HF|].
      split;[exists p;auto|]. split;[exists q;auto|exact HV].
Qed.

Lemma sr_invalid_relation M f h a b :
  (f=zeroM M \/ sf_invalid M f) -> sf_relation M h a b f -> False.
Proof.
  intros [HZ|HI] HF.
  - exact (sf_relation_nonzero M h a b f HF HZ).
  - exact (sf_invalid_not_constructor M h a b f HI HF).
Qed.

Lemma sr_atom_quantifier_distinct equality universal :
  sr_source_atom equality <> sr_source_quantifier universal.
Proof. destruct equality,universal;discriminate. Qed.
Lemma sr_atom_binary_distinct equality h : sf_binary h -> sr_source_atom equality<>h.
Proof. intros [H|[H|H]];subst h;destruct equality;discriminate. Qed.
Lemma sr_quantifier_binary_distinct universal h : sf_binary h -> sr_source_quantifier universal<>h.
Proof. intros [H|[H|H]];subst h;destruct universal;discriminate. Qed.
Lemma sr_source_quantifier_injective x y : sr_source_quantifier x=sr_source_quantifier y -> x=y.
Proof. destruct x,y;cbn;congruence. Qed.
Lemma sr_binary_second M h b : sf_binary h -> sf_payload_second M h b=b.
Proof. intros [H|[H|H]];subst h;reflexivity. Qed.

Theorem source_relativization_invalid_inv M d f v :
  (f=zeroM M \/ sf_invalid M f) -> source_relativization M d f v -> v=zeroM M.
Proof.
  intros HBad H. apply source_relativization_cases in H.
  destruct H as [[[HB HV]|[a [b [[HF|HF] HV]]]]|[[univ [a [w [HF HH]]]]|[h [a [b [x [y [Hh [HF HH]]]]]]]]];
    try exact HV;exfalso;eapply sr_invalid_relation;eassumption.
Qed.

Theorem source_relativization_atom_inv M d equality a b f v :
  sf_relation M (sr_source_atom equality) a b f -> source_relativization M d f v -> v=f.
Proof.
  intros HF H. apply source_relativization_cases in H.
  destruct H as [[[HB HV]|[a' [b' [HH HV]]]]|[[univ [a' [w [HH _]]]]|[h [a' [b' [x [y [Hh [HH _]]]]]]]]];
    try exact HV.
  - exfalso;eapply sr_invalid_relation;eassumption.
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HH) as [E _].
    exfalso;exact (sr_atom_quantifier_distinct equality univ E).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HH) as [E _].
    exfalso;exact (sr_atom_binary_distinct equality h Hh E).
Qed.

Theorem source_relativization_binary_inv M d h a b f v :
  sf_binary h -> sf_relation M h a b f -> source_relativization M d f v ->
  exists x y,source_relativization M d a x /\ source_relativization M d b y /\ sf_relation M h x y v.
Proof.
  intros Hh HF H. apply source_relativization_cases in H.
  destruct H as [[[HB HV]|[a' [b' [[HH|HH] HV]]]]|[[univ [a' [w [HH HC]]]]|[h' [a' [b' [x [y [Hh' [HH [HX [HY HO]]]]]]]]]]].
  - exfalso;eapply sr_invalid_relation;eassumption.
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HH HF) as [E _].
    exfalso;exact (sr_atom_binary_distinct false h Hh E).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HH HF) as [E _].
    exfalso;exact (sr_atom_binary_distinct true h Hh E).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HH HF) as [E _].
    exfalso;exact (sr_quantifier_binary_distinct univ h Hh E).
  - destruct (sf_relation_injective M h h' a b a' b' f HF HH) as [EH [EA EB]].
    subst h' a'. rewrite !sr_binary_second in EB by exact Hh. subst b'. exists x,y;auto.
Qed.

Theorem source_relativization_quantifier_inv M d universal a f v :
  sf_relation M (sr_source_quantifier universal) a (zeroM M) f ->
  source_relativization M d f v ->
  exists w,source_relativization M d a w /\ sr_quantifier M universal d w v.
Proof.
  intros HF H. apply source_relativization_cases in H.
  destruct H as [[[HB HV]|[a' [b' [[HH|HH] HV]]]]|[[univ [a' [w [HH [HC HO]]]]]|[h [a' [b' [x [y [Hh [HH HC]]]]]]]]].
  - exfalso;eapply sr_invalid_relation;eassumption.
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HH HF) as [E _].
    exfalso;exact (sr_atom_quantifier_distinct false universal E).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HH HF) as [E _].
    exfalso;exact (sr_atom_quantifier_distinct true universal E).
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HH) as [E [EA EB]].
    apply sr_source_quantifier_injective in E. subst univ a'. exists w;auto.
  - destruct (sf_relation_injective M _ _ _ _ _ _ _ HF HH) as [E _].
    exfalso;exact (sr_quantifier_binary_distinct universal h Hh E).
Qed.

Lemma sr_quantifier_functional M universal d w v v' :
  sr_quantifier M universal d w v -> sr_quantifier M universal d w v' -> v=v'.
Proof.
  intros [mid [HM HV]] [mid' [HM' HV']].
  assert (E:mid=mid') by exact (sf_relation_functional M _ d w mid mid' HM HM').
  subst mid'. exact (sf_relation_functional M _ mid (zeroM M) v v' HV HV').
Qed.

Definition sr_functional_at M f := forall d v w,
  source_relativization M d f v -> source_relativization M d f w -> v=w.
Definition sr_functionality_formula : form :=
  ∀∀∀ (source_relativization_formula $2 $3 $1 →
    source_relativization_formula $2 $3 $0 → $1==$0).
Local Opaque holds source_relativization_formula.
Lemma sr_functional_at_definable M : Definable1 M (sr_functional_at M).
Proof.
  exists sr_functionality_formula,(fun _=>zeroM M). intro f.
  unfold sr_functionality_formula,sr_functional_at.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite source_relativization_formula_correct.
  setoid_rewrite fresh_holds_eq. reflexivity.
Qed.

Theorem source_relativization_functional M f : sr_functional_at M f.
Proof.
  revert f. apply (sf_code_induction M (sr_functional_at M)).
  - apply sr_functional_at_definable.
  - intros d v w HV HW. rewrite (source_relativization_invalid_inv M d (zeroM M) v (or_introl eq_refl) HV).
    symmetry. exact (source_relativization_invalid_inv M d (zeroM M) w (or_introl eq_refl) HW).
  - intros f HF d v w HV HW. rewrite (source_relativization_invalid_inv M d f v (or_intror HF) HV).
    symmetry. exact (source_relativization_invalid_inv M d f w (or_intror HF) HW).
  - intros a b f HF d v w HV HW. rewrite (source_relativization_atom_inv M d false a b f v HF HV).
    symmetry. exact (source_relativization_atom_inv M d false a b f w HF HW).
  - intros a b f HF d v w HV HW. rewrite (source_relativization_atom_inv M d true a b f v HF HV).
    symmetry. exact (source_relativization_atom_inv M d true a b f w HF HW).
  - intros h a b f HH HF IHa IHb d v w HV HW.
    destruct (source_relativization_binary_inv M d h a b f v HH HF HV) as [x [y [HX [HY HO]]]].
    destruct (source_relativization_binary_inv M d h a b f w HH HF HW) as [x' [y' [HX' [HY' HO']]]].
    assert (EX:x=x') by exact (IHa d x x' HX HX').
    assert (EY:y=y') by exact (IHb d y y' HY HY'). subst x' y'.
    exact (sf_relation_functional M h x y v w HO HO').
  - intros h a f HH HF IH d v w HV HW.
    destruct HH as [HH|HH];subst h.
    + destruct (source_relativization_quantifier_inv M d true a f v HF HV) as [x [HX HO]].
      destruct (source_relativization_quantifier_inv M d true a f w HF HW) as [y [HY HO']].
      assert (E:x=y) by exact (IH d x y HX HY). subst y.
      exact (sr_quantifier_functional M true d x v w HO HO').
    + destruct (source_relativization_quantifier_inv M d false a f v HF HV) as [x [HX HO]].
      destruct (source_relativization_quantifier_inv M d false a f w HF HW) as [y [HY HO']].
      assert (E:x=y) by exact (IH d x y HX HY). subst y.
      exact (sr_quantifier_functional M false d x v w HO HO').
Qed.

Print Assumptions source_relativization_cases.
Print Assumptions source_relativization_binary_inv.
Print Assumptions source_relativization_quantifier_inv.
Print Assumptions source_relativization_functional.
