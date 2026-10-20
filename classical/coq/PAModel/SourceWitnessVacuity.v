(** The negative witness-existence branch proves a universal witness
    request by ordinary source explosion and actual universal introduction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceSequents
  NumericalContexts NumericalContextRenaming NumericalRenaming NumericalSourceFull SourceQuantifierRules
  SourceProofRenaming SourcePropositionalTemplates SourceFunctionalityShells SetSchemaConstructors.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_vacuous_witness_template :=SPTImpl (SPTSlot 1)
  (SPTImpl (SPTSlot 0) (SPTSlot 2)).
Theorem source_vacuous_witness_program :source_prop_program
  [SPTImpl (SPTSlot 0) SPTFalse] source_vacuous_witness_template.
Proof.
  apply SPTII,SPTII,SPTExp. eapply SPTIE.
  - apply SPTCtx. now right;right;left.
  - apply SPTCtx. now left.
Qed.

Theorem source_full_vacuous_witness_all M b c n test shiftedTest neg level right ew point all :
  source_formula_shift M test shiftedTest ->sf_relation M SFImpl test (zeroM M) neg ->
  sf_relation M SFImpl shiftedTest right ew ->sf_relation M SFImpl level ew point ->
  sf_relation M SFAll point (zeroM M) all ->source_sequent_wf M b c n all ->
  source_full_prv M b c n neg ->source_full_prv M b c n all.
Proof.
  intros HShift HNeg HEw HPoint HAll [k [HAllBound HCtx]] PNeg.
  pose proof (proj1 (source_bounded_accept_unary M SFAll point all k
    (or_introl eq_refl) HAll) HAllBound) as HPointBound.
  destruct (proj1 (source_bounded_accept_binary M SFImpl level ew point (succM M k)
    (or_intror (or_intror eq_refl)) HPoint) HPointBound) as (HL&HE).
  destruct (proj1 (source_bounded_accept_binary M SFImpl shiftedTest right ew (succM M k)
    (or_intror (or_intror eq_refl)) HEw) HE) as (HT&HR).
  destruct (context_shift_total M b c n) as (sb&sc&HCtxShift).
  destruct (sf_relation_total M SFImpl shiftedTest (zeroM M)) as (shiftedNeg&HShiftedNeg).
  assert (HNegShift:source_formula_shift M neg shiftedNeg).
  { apply (proj2 (numerical_renaming_binary M SFImpl test (zeroM M) neg (zeroM M) (zeroM M)
      (zeroM M) (code_numeral M 1) shiftedNeg (or_intror (or_intror eq_refl)) HNeg)).
    exists shiftedTest,(zeroM M). split;[exact HShift|]. split;[|exact HShiftedNeg].
    exact (proj2 (numerical_renaming_invalid M (zeroM M) (zeroM M) (zeroM M) (zeroM M)
      (code_numeral M 1) (zeroM M) (or_introl eq_refl)) eq_refl). }
  pose proof (source_full_prv_renaming M b c n neg (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 1) sb sc shiftedNeg PNeg HCtxShift HNegShift) as PN.
  apply (full_source_AllI M b c n point all sb sc (ex_intro _ k (conj HAllBound HCtx)));
    [|exact HCtxShift|exact HAll].
  apply (source_prop_program_sound M _ _ source_vacuous_witness_program
    (schema_env3 shiftedTest level right) (succM M k) sb sc n point).
  - intros [|[|i]];cbn [schema_env3];assumption.
  - exact (context_shift_preserves_bound M b c n sb sc k HCtxShift HCtx).
  - intros a [<-|[]] f HF.
    assert (HCode:code_relation M (schema_env3 shiftedTest level right)
      (source_prop_expression (SPTImpl (SPTSlot 0) SPTFalse)) shiftedNeg).
    { exact (source_prop_template_join M _ SFImpl (SPTSlot 0) SPTFalse shiftedTest (zeroM M)
        shiftedNeg eq_refl eq_refl HShiftedNeg). }
    pose proof (code_relation_functional M _ _ f shiftedNeg HF HCode) as E. now subst f.
  - unfold source_vacuous_witness_template,source_prop_expression. functionality_graph.
Qed.

Print Assumptions source_vacuous_witness_program.
Print Assumptions source_full_vacuous_witness_all.
