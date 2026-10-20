(** The same raw Separation witness is WF, and its actual profile restricts
    to WF. The matrix code may be nonstandard and may contain arbitrary parameters. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SchemaConstructorBounds SourceNumeralLift
  NumericalContexts NumericalSourceFull SourceRelativizationBounds
  SourceWFFormula NumericalWFFoundation WFSubsetCore WFSubsetInstantiation
  SourcePropositionalTemplates SourceSeparationSubset SourceUniversalGuard.
From Undecidability.FOL Require Import Sets.minZF Syntax.Core.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
Open Scope minZFsyn.

Definition source_sep_left : sf_form := $0 ∈' $1.
Definition source_sep_right : sf_form := $0 ∈' $2.
Definition source_sep_subset_body : sf_form := source_sep_left → source_sep_right.
Definition source_sep_left_code M := code_numeral M (sf_encode source_sep_left).
Definition source_sep_right_code M := code_numeral M (sf_encode source_sep_right).
Definition source_sep_subset_body_code M := code_numeral M (sf_encode source_sep_subset_body).
Definition source_sep_subset_code M := code_numeral M (sf_encode (wf_subset $0 $1)).

Lemma source_formula_universal_numeral M (phi:sf_form) :
  sf_relation M SFAll (code_numeral M (sf_encode phi)) (zeroM M)
    (code_numeral M (sf_encode (∀ phi))).
Proof. exact (sf_make_numeral M SFAll (sf_encode phi) 0). Qed.

Lemma source_sep_subset_graphs M :
  sf_relation M SFImpl (source_sep_left_code M) (source_sep_right_code M)
    (source_sep_subset_body_code M) /\
  sf_relation M SFAll (source_sep_subset_body_code M) (zeroM M) (source_sep_subset_code M).
Proof.
  split;[exact (source_formula_implication_numeral M source_sep_left source_sep_right)|].
  assert (E:wf_subset $0 $1=∀ source_sep_subset_body) by reflexivity.
  unfold source_sep_subset_code. rewrite E.
  exact (source_formula_universal_numeral M source_sep_subset_body).
Qed.

Lemma source_sep_atom_bounds M n :
  source_bounded M (source_sep_left_code M) (succM M (succM M (succM M n))) /\
  source_bounded M (source_sep_right_code M) (succM M (succM M (succM M n))).
Proof.
  assert (HL:sf_relation M SFMember (code_numeral M 0) (code_numeral M 1) (source_sep_left_code M)).
  { exact (sf_make_numeral M SFMember 0 1). }
  assert (HR:sf_relation M SFMember (code_numeral M 0) (code_numeral M 2) (source_sep_right_code M)).
  { exact (sf_make_numeral M SFMember 0 2). }
  split.
  - apply (proj2 (source_bounded_accept_atom M SFMember _ _ _ _ (or_introl eq_refl) HL)).
    split;schema_small_index.
  - apply (proj2 (source_bounded_accept_atom M SFMember _ _ _ _ (or_introl eq_refl) HR)).
    split;schema_small_index.
Qed.

Theorem source_full_WF_separation_witness M b c l n theta point profile guardpoint guardprofile witness :
  context_bounded M b c l (succM M (succM M n)) ->
  source_bounded M theta (succM M (succM M (succM M n))) ->
  code_relation M (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
    (source_prop_expression separation_point_template) point ->
  sf_relation M SFAll point (zeroM M) profile ->
  sf_relation M SFImpl (source_wf_domain_code M) point guardpoint ->
  sf_relation M SFAll guardpoint (zeroM M) guardprofile ->
  sf_relation M SFAnd (source_wf_domain_code M) guardprofile witness ->
  source_full_prv M b c l (source_wf_subset_code M) ->
  source_full_prv M b c l (code_numeral M (sf_encode (wf_class $1))) ->
  source_full_prv M b c l profile -> source_full_prv M b c l witness.
Proof.
  intros HC HTheta HPoint HProfile HGuard HGuardProfile HWitness PSubset PX PProfile.
  destruct (source_sep_atom_bounds M n) as [HL HR].
  destruct (source_sep_subset_graphs M) as [HSubsetBody HSubsetAll].
  pose proof (source_full_separation_subset_projection M b c l (succM M (succM M n))
    (source_sep_left_code M) (source_sep_right_code M) theta point profile
    (source_sep_subset_body_code M) (source_sep_subset_code M)
    HC HL HR HTheta HPoint HProfile HSubsetBody HSubsetAll PProfile) as PSub.
  pose proof (@numerical_wf_subset_at_witness M b c l PSubset PX PSub) as PWF.
  pose proof (source_full_universal_guard M (source_wf_domain_code M) b c l point profile
    guardpoint guardprofile (numerical_wf_domain_bounded M) HProfile HGuard HGuardProfile PProfile) as PGuard.
  apply (full_source_CI M b c l (source_wf_domain_code M) guardprofile witness);[|exact PWF|exact PGuard|exact HWitness].
  assert (HPointBound:source_bounded M point (succM M (succM M (succM M n)))).
  { apply (source_prop_template_bound M
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
      separation_point_template (succM M (succM M (succM M n)))) with (f:=point).
    - intros [|[|i]];[exact HL|exact HR|exact HTheta].
    - exact HPoint. }
  exists (succM M (succM M n)). split;[|exact HC].
  apply (proj2 (source_bounded_accept_binary M SFAnd (source_wf_domain_code M) guardprofile witness
    (succM M (succM M n)) (or_introl eq_refl) HWitness)). split.
  - exact (sr_domain_bound_succ M (source_wf_domain_code M) (succM M n) (numerical_wf_domain_bounded M)).
  - apply (proj2 (source_bounded_accept_unary M SFAll guardpoint guardprofile
      (succM M (succM M n)) (or_introl eq_refl) HGuardProfile)).
    apply (proj2 (source_bounded_accept_binary M SFImpl (source_wf_domain_code M) point guardpoint
      (succM M (succM M (succM M n))) (or_intror (or_intror eq_refl)) HGuard)). split;[|exact HPointBound].
    exact (sr_domain_bound_succ M (source_wf_domain_code M) (succM M (succM M n))
      (numerical_wf_domain_bounded M)).
Qed.

Print Assumptions source_sep_subset_graphs.
Print Assumptions source_full_WF_separation_witness.
