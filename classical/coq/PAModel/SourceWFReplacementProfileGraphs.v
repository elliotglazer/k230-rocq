From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SchemaConstructorBounds SourceNumeralLift
  SourceDomainInstances NumericalInstantiation SourceRelativizationBounds
  SourceWFFormula NumericalWFFoundation SourceWFSeparationWitness SourceWFSeparationExistential
  SourcePropositionalTemplates SourcePropositionalRebase SourceWFReplacementBody
  SourceWFReplacementExistential SourceWFReplacementProfiles.
From Undecidability.FOL Require Import Sets.minZF.
Unset Implicit Arguments.
Open Scope minZFsyn.

Definition source_rep_input : sf_form := $0 ∈' $3.
Definition source_rep_input_code M := code_numeral M (sf_encode source_rep_input).

Lemma source_rep_atom_graphs M env :
  code_relation M env (E_sf_mem 0 1) (source_sep_left_code M) /\
  code_relation M env (E_sf_mem 0 3) (source_rep_input_code M).
Proof.
  split.
  - apply (proj2 (schema_expression_graph M env SFMember (CEconst 0) (CEconst 1)
      (code_numeral M 0) (code_numeral M 1) (source_sep_left_code M) eq_refl eq_refl)).
    exact (sf_make_numeral M SFMember 0 1).
  - apply (proj2 (schema_expression_graph M env SFMember (CEconst 0) (CEconst 3)
      (code_numeral M 0) (code_numeral M 3) (source_rep_input_code M) eq_refl eq_refl)).
    exact (sf_make_numeral M SFMember 0 3).
Qed.

Lemma source_rep_input_bound M n :
  source_bounded M (source_rep_input_code M) (succM M (succM M (succM M (succM M n)))).
Proof.
  apply (proj2 (source_bounded_accept_atom M SFMember (code_numeral M 0) (code_numeral M 3)
    (source_rep_input_code M) _ (or_introl eq_refl) (sf_make_numeral M SFMember 0 3))).
  split;schema_small_index.
Qed.

Lemma source_rep_domain1_bound M n :
  source_bounded M (source_wf_domain1_code M) (succM M (succM M n)).
Proof.
  apply (source_domain_instance_bound M (source_wf_domain_code M) (code_numeral M 1)
    (source_wf_domain1_code M) _ (numerical_wf_domain_bounded M));[schema_small_index|].
  exact (source_domain_instance_shift M (source_wf_domain_code M) (zeroM M) (source_wf_domain_code M)
    (source_wf_domain1_code M) (numerical_wf_domain_bounded M)
    (source_domain_instance_zero M _ (numerical_wf_domain_bounded M)) (source_wf_domain_shift M)).
Qed.

Local Opaque source_wf_domain_code source_wf_domain1_code source_rep_input_code.

Lemma source_rep_body_rebase M theta a body :
  code_relation M (wf_rep_profile_env M theta)
    (source_prop_expression_with
      (fun i=>match i with 0=>CEvar 0|1=>CEvar 1|2=>E_sf_mem 0 3|_=>CEvar 2 end) a) body <->
  code_relation M (wf_rep_env (source_wf_domain_code M) (source_wf_domain1_code M)
    (source_rep_input_code M) theta) (source_prop_expression a) body.
Proof.
  apply source_prop_expression_with_graph. intros [|[|[|i]]];cbn [wf_rep_env wf_rep_profile_env schema_env3];try reflexivity.
  exact (proj2 (source_rep_atom_graphs M _)).
Qed.

Lemma schema_iff_split M env A B a b f :
  code_relation M env A a ->code_relation M env B b ->code_relation M env (E_sf_iff A B) f ->
  exists forward reverse,sf_relation M SFImpl a b forward /\sf_relation M SFImpl b a reverse /\
    sf_relation M SFAnd forward reverse f.
Proof.
  intros HA HB HF. unfold E_sf_iff in HF.
  destruct (schema_expression_split M env SFAnd _ _ f HF) as [forward [reverse [HFor [HRev HAnd]]]].
  exists forward,reverse. split;[|split;[|exact HAnd]].
  - exact (proj1 (schema_expression_graph M env SFImpl A B a b forward HA HB) HFor).
  - exact (proj1 (schema_expression_graph M env SFImpl B A b a reverse HB HA) HRev).
Qed.

Lemma source_wf_rep_target_profile_bound M theta target n :
  source_bounded M theta (succM M (succM M (succM M (succM M n)))) ->
  source_wf_rep_target_profile_graph M theta target ->source_bounded M target (succM M (succM M n)).
Proof.
  intros HT HF. unfold source_wf_rep_target_profile_graph in HF.
  assert (HB:schema_expression_bound M (wf_rep_profile_env M theta)
    (E_wf_rep_target_profile (CEvar 0) (CEvar 2)) (succM M (succM M n))).
  { unfold E_wf_rep_target_profile,E_sf_all,E_sf_ex,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index;cbn [wf_rep_profile_env schema_env3];try exact HT;
      apply sr_domain_bound_succ;apply numerical_wf_domain_bounded. }
  exact (HB target HF).
Qed.

Print Assumptions source_rep_atom_graphs.
Print Assumptions source_rep_domain1_bound.
Print Assumptions source_rep_body_rebase.
Print Assumptions source_wf_rep_target_profile_bound.
