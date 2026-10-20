(** Whole finite-template rebasing. The hygiene condition allows free names
    above the allocation base, provided they avoid the allocated binders.
    This stronger condition survives conversion through a common high name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions CodeDescent CodeTags NumericalProofs ProofTemplates NamedLeibnizSteps
  NamedAlpha NamedExistential NamedSubstitution NamedBinderFresh FreshNames
  NumericalEquivalence FiniteTemplateEvaluation TemplateAlpha TemplateExistsAlpha
  TemplateNamedExclusions TemplateBinderRange TemplateBinderFresh
  QuotientAtomTemplates QuotationPayloads.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Definition template_hygienic M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) (eta : nat -> carrier M) k :=
  template_allocations_avoid M phi k (zeroM M) /\
  forall i,template_allocations_avoid M phi k (eta i).

Lemma template_hygienic_below M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k :
  coding_lt M (zeroM M) k -> (forall i,coding_lt M (eta i) k) ->
  template_hygienic M phi eta k.
Proof.
  intros Hzero HE. split.
  - now apply template_allocations_avoid_below.
  - intro i. apply template_allocations_avoid_below,HE.
Qed.

Lemma template_hygienic_common_child M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k y q :
  template_hygienic M (quant q phi) eta k ->
  template_allocations_avoid M phi (succM M k) y ->
  template_hygienic M phi (y .: eta) (succM M k).
Proof.
  intros [[Hk Hzero] HE] HY. split;[exact Hzero|].
  intros [|i];[exact HY|exact (proj2 (HE i))].
Qed.

Section CommonName.
Variable M : Model.
Add Ring template_rebase_ring : (model_semiring M).
Lemma template_common_fresh {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) k l f g :
  exists y,coding_lt M f y /\ coding_lt M g y /\ coding_lt M k y /\ coding_lt M l y /\
    template_allocations_avoid M phi k y /\ template_allocations_avoid M phi l y.
Proof.
  set (y:=succM M (addM M (addM M f g)
    (addM M (addM M k l) (code_numeral M (template_binder_span phi))))).
  exists y. split.
  - exists (addM M g (addM M (addM M k l) (code_numeral M (template_binder_span phi)))).
    unfold y. f_equal. ring.
  - split.
    + exists (addM M f (addM M (addM M k l) (code_numeral M (template_binder_span phi)))).
      unfold y. f_equal. ring.
    + split.
      * exists (addM M (addM M f g) (addM M l (code_numeral M (template_binder_span phi)))).
        unfold y. f_equal. ring.
      * split.
        -- exists (addM M (addM M f g) (addM M k (code_numeral M (template_binder_span phi)))).
           unfold y. f_equal. ring.
        -- split;apply template_allocations_avoid_offsets;intros i Hi.
           ++ assert (E : template_binder_span phi=i+(template_binder_span phi-i)) by lia.
              assert (EN : code_numeral M (template_binder_span phi) =
                addM M (code_numeral M i) (code_numeral M (template_binder_span phi-i))).
              { rewrite E at 1. apply template_numeral_add. }
              assert (Hlt : coding_lt M (addM M k (code_numeral M i)) y).
              { exists (addM M (addM M f g) (addM M l (code_numeral M (template_binder_span phi-i)))).
                unfold y. rewrite EN. f_equal. ring. }
              exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
                (fun ax H rho=>axioms M ax rho H) _ _ Hlt).
           ++ assert (E : template_binder_span phi=i+(template_binder_span phi-i)) by lia.
              assert (EN : code_numeral M (template_binder_span phi) =
                addM M (code_numeral M i) (code_numeral M (template_binder_span phi-i))).
              { rewrite E at 1. apply template_numeral_add. }
              assert (Hlt : coding_lt M (addM M l (code_numeral M i)) y).
              { exists (addM M (addM M f g) (addM M k (code_numeral M (template_binder_span phi-i)))).
                unfold y. rewrite EN. f_equal. ring. }
              exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
                (fun ax H rho=>axioms M ax rho H) _ _ Hlt).
Qed.
End CommonName.

Lemma template_quantified_equivalent M universal x a b f g :
  numerical_equivalent M a b -> template_quantified M universal x a f ->
  template_quantified M universal x b g -> numerical_equivalent M f g.
Proof.
  intros HAB HF HG. set (rho:=x .: a .: b .: fun _=>zeroM M).
  assert (HE : expression_equivalent M rho (CEvar 1) (CEvar 2)).
  { exact (proj2 (numerical_equivalent_expression M rho (CEvar 1) (CEvar 2) a b eq_refl eq_refl) HAB). }
  destruct universal.
  - apply (proj1 (numerical_equivalent_expression M rho
      (E_wal (CEvar 0) (CEvar 1)) (E_wal (CEvar 0) (CEvar 2)) f g
      (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF)
      (proj2 (template_quantified_graph M rho true (CEvar 0) (CEvar 2) x b g eq_refl eq_refl) HG))).
    now apply expression_equivalent_all.
  - apply (proj1 (numerical_equivalent_expression M rho
      (E_wex (CEvar 0) (CEvar 1)) (E_wex (CEvar 0) (CEvar 2)) f g
      (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF)
      (proj2 (template_quantified_graph M rho false (CEvar 0) (CEvar 2) x b g eq_refl eq_refl) HG))).
    now apply expression_equivalent_exists.
Qed.

Lemma template_quantified_total M (universal : bool) x a : exists f,template_quantified M universal x a f.
Proof.
  destruct (code_relation_total M (if universal then E_wal (CEvar 0) (CEvar 1)
    else E_wex (CEvar 0) (CEvar 1)) (x .: a .: fun _=>zeroM M)) as [f HF].
  exists f. exact (proj1 (template_quantified_graph M (x .: a .: fun _=>zeroM M) universal (CEvar 0) (CEvar 1) x a f eq_refl eq_refl) HF).
Qed.

Lemma template_evaluation_outer_alpha M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k y a v f g universal :
  k<>zeroM M -> k<>y -> y<>zeroM M -> (forall i,eta i<>k) ->
  template_allocations_avoid M phi (succM M k) y ->
  coding_lt M a y ->
  template_evaluation M phi (k .: eta) (succM M k) a ->
  template_evaluation M phi (y .: eta) (succM M k) v ->
  template_quantified M universal k a f -> template_quantified M universal y v g ->
  numerical_equivalent M f g.
Proof.
  intros Hk Hky Hy HE HY Hay HA HV HF HG.
  pose proof (alpha_template_substitution M phi eta (succM M k) k y a v Hk HE
    (template_allocations_avoid_below M phi (succM M k) k (coding_lt_succ M k)) HY
    (proj2 (template_evaluation_alpha_body M phi eta (succM M k) k a) HA)
    (proj2 (template_evaluation_alpha_body M phi eta (succM M k) y v) HV)) as HS.
  pose proof (template_evaluation_binder_exclusion M phi (k .: eta) (succM M k) k a
    (template_allocations_avoid_below M phi (succM M k) k (coding_lt_succ M k)) HA) as HB.
  pose proof (formula_above_is_fresh M a y Hay) as Hfresh.
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (f .: g .: fun _=>zeroM M)) as [forward Hforward].
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 1))
    (g .: f .: fun _=>zeroM M)) as [backward Hbackward].
  destruct universal.
  - destruct (numerical_named_alpha M a k y v f g forward backward
      Hky HB Hfresh HS HF HG Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
  - destruct (numerical_named_exists_alpha M a k y v f g forward backward
      Hk Hy Hky HB Hfresh HS HF HG Hforward Hbackward) as [PF PB].
    exact (numerical_equivalent_of_proofs M f g forward backward Hforward Hbackward PF PB).
Qed.

Theorem finite_template_rebase M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall eta k l f g,
    template_hygienic M phi eta k -> template_hygienic M phi eta l ->
    template_evaluation M phi eta k f -> template_evaluation M phi eta l g ->
    numerical_equivalent M f g.
Proof.
  induction phi as [|flag P args|flag op a IHa b IHb|flag q a IH];
    intros eta k l f g HK HL HF HG.
  - cbn [template_evaluation] in HF,HG. subst f g. apply numerical_equivalent_refl.
  - cbn [template_evaluation] in HF,HG.
    assert (f=g) by (eapply tagged_pair_functional;eassumption). subst g.
    apply numerical_equivalent_refl.
  - destruct HK as [[HkA HkB] HkE],HL as [[HlA HlB] HlE].
    destruct HF as [x [y [HX [HY HF]]]],HG as [x' [y' [HX' [HY' HG]]]].
    apply (numerical_equivalent_binary M (template_binary_head op) x y x' y' f g);try assumption.
    + apply (IHa eta k l x x');try assumption;split;[exact HkA|intro i;exact (proj1 (HkE i))|exact HlA|intro i;exact (proj1 (HlE i))].
    + apply (IHb eta k l y y');try assumption;split;[exact HkB|intro i;exact (proj2 (HkE i))|exact HlB|intro i;exact (proj2 (HlE i))].
  - destruct HF as [x [HX HF]],HG as [z [HZ HG]].
    destruct (template_common_fresh M a (succM M k) (succM M l) x z)
      as [y [Hxy [Hzy [Hky [Hly [HAk HAl]]]]]].
    destruct (template_evaluation_total M a (y .: eta) (succM M k)) as [v HV].
    destruct (template_evaluation_total M a (y .: eta) (succM M l)) as [w HW].
    destruct (template_quantified_total M (match q with All=>true|Ex=>false end) y v) as [f' HF'].
    destruct (template_quantified_total M (match q with All=>true|Ex=>false end) y w) as [g' HG'].
    assert (Hk0 : k<>zeroM M) by exact (proj1 (proj1 HK)).
    assert (Hl0 : l<>zeroM M) by exact (proj1 (proj1 HL)).
    assert (Hy0 : y<>zeroM M).
    { intro E. subst y. exact (coding_not_lt_zero M x Hxy). }
    assert (HkY : k<>y).
    { exact (@Peano.lt_neq (carrier M) (raw_interpretation M) (fun ax H rho=>axioms M ax rho H)
      k y (coding_lt_trans M k (succM M k) y (coding_lt_succ M k) Hky)). }
    assert (HlY : l<>y).
    { exact (@Peano.lt_neq (carrier M) (raw_interpretation M) (fun ax H rho=>axioms M ax rho H)
      l y (coding_lt_trans M l (succM M l) y (coding_lt_succ M l) Hly)). }
    apply (numerical_equivalent_trans M f f' g).
    + apply (template_evaluation_outer_alpha M a eta k y x v f f'
        (match q with All=>true|Ex=>false end));try assumption.
      intros i E. apply (proj1 (proj2 HK i)). symmetry. exact E.
    + apply (numerical_equivalent_trans M f' g' g).
      * apply (template_quantified_equivalent M (match q with All=>true|Ex=>false end) y v w f' g');try assumption.
        apply (IH (y .: eta) (succM M k) (succM M l) v w);try assumption.
        -- exact (template_hygienic_common_child M a eta k y q HK HAk).
        -- exact (template_hygienic_common_child M a eta l y q HL HAl).
      * apply numerical_equivalent_sym.
        apply (template_evaluation_outer_alpha M a eta l y z w g g'
          (match q with All=>true|Ex=>false end));try assumption.
        intros i E. apply (proj1 (proj2 HL i)). symmetry. exact E.
Qed.

Print Assumptions finite_template_rebase.
