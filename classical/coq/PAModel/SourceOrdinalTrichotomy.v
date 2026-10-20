(** Actual ZFR trichotomy at arbitrary internal variable names, with
    the literal fixed source graph exposed for numerical proof assembly. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift SourceOrdinalTrichotomyOld
  SourceOrdinalPredicate SourceOrdinalParameterCalibration SourceFiniteParameters SourceFiniteParameterProofs
  SourceZFRProvability SourceDescriptorProvability SourceSetTheoryDescriptors
  SourcePropositionalRebase NumericalInstantiation SubstitutionSource.
From OldZFC Require Z_base.
Unset Implicit Arguments.

Definition source_ordinal_trichotomy := isolated_formula old_ordinal_trichotomy_law.
Definition source_ordinal_second := isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 1)).
Definition ordinal_trichotomy_expression :=
  source_parameter_expression source_three_parameter_names source_ordinal_trichotomy.

Theorem source_zfr_ordinal_trichotomy M rho law :
  code_relation M rho ordinal_trichotomy_expression law ->source_zfr_provable M law.
Proof.
  intro HG. apply (proj1 (source_zfr_descriptor_provable M law)).
  apply (source_descriptor_three_parameter_proof M ZFRSourceDescriptor source_ordinal_trichotomy rho law).
  - apply (proj2 (source_zfr_descriptor_provable M _)).
    exact (finite_old_zfr_proof_lift M old_trichotomy_background old_ordinal_trichotomy_law
      old_trichotomy_background_valid old_ordinal_trichotomy_law_proof).
  - exact HG.
Qed.

Lemma ordinal_trichotomy_expression_shape : ordinal_trichotomy_expression =
  E_sf SFImpl (source_parameter_expression source_three_parameter_names source_ordinal_predicate)
    (E_sf SFImpl (source_parameter_expression source_three_parameter_names source_ordinal_second)
      (E_sf SFOr (E_sf SFOr (E_sf SFMember (CEvar 0) (CEvar 1))
        (E_sf SFEqual (CEvar 0) (CEvar 1))) (E_sf SFMember (CEvar 1) (CEvar 0)))).
Proof. reflexivity. Qed.

Theorem source_ordinal_trichotomy_shell M rho law :
  code_relation M rho ordinal_trichotomy_expression law ->
  exists ordA ordB implication tri first left equal right,
    numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA /\
    numerical_instantiation M (source_ordinal_predicate_code M) (rho 1) ordB /\
    sf_relation M SFImpl ordA implication law /\
    sf_relation M SFImpl ordB tri implication /\
    sf_relation M SFOr first right tri /\sf_relation M SFOr left equal first /\
    sf_relation M SFMember (rho 0) (rho 1) left /\
    sf_relation M SFEqual (rho 0) (rho 1) equal /\
    sf_relation M SFMember (rho 1) (rho 0) right.
Proof.
  intro HG. rewrite ordinal_trichotomy_expression_shape in HG.
  destruct (schema_expression_split M rho SFImpl _ _ law HG) as (ordA&implication&HA&HI&HLaw).
  destruct (schema_expression_split M rho SFImpl _ _ implication HI) as (ordB&tri&HB&HT&HImp).
  destruct (schema_expression_split M rho SFOr _ _ tri HT) as (first&right&HF&HR&HTri).
  destruct (schema_expression_split M rho SFOr _ _ first HF) as (left&equal&HL&HE&HFirst).
  assert (HIA:numerical_instantiation M (source_ordinal_predicate_code M) (rho 0) ordA).
  { exact (source_parameter_ordinal_instance M source_three_parameter_names rho 0 (rho 0) ordA eq_refl HA). }
  assert (HIB:numerical_instantiation M (source_ordinal_predicate_code M) (rho 1) ordB).
  { exact (source_parameter_ordinal_instance M source_three_parameter_names rho 1 (rho 1) ordB eq_refl HB). }
  assert (HLG:sf_relation M SFMember (rho 0) (rho 1) left).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEvar 0) (CEvar 1)
      (rho 0) (rho 1) left eq_refl eq_refl) HL). }
  assert (HEG:sf_relation M SFEqual (rho 0) (rho 1) equal).
  { exact (proj1 (substitution_source_constructor_graph M rho SFEqual (CEvar 0) (CEvar 1)
      (rho 0) (rho 1) equal eq_refl eq_refl) HE). }
  assert (HRG:sf_relation M SFMember (rho 1) (rho 0) right).
  { exact (proj1 (substitution_source_constructor_graph M rho SFMember (CEvar 1) (CEvar 0)
      (rho 1) (rho 0) right eq_refl eq_refl) HR). }
  exists ordA,ordB,implication,tri,first,left,equal,right. repeat split;assumption.
Qed.

Print Assumptions source_zfr_ordinal_trichotomy.
Print Assumptions source_ordinal_trichotomy_shell.
