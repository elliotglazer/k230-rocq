(** The raw Separation witness is retained by the WF interpretation.
    All matrix and context codes may be nonstandard. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceBoundMonotone SchemaConstructorBounds
  SourceNumeralLift NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalSourceFull SourceProofRenaming SourceProofWeakening SourceContextTransport
  SourceTraceBounds SourceQuantifierRules NumericalRenaming SourceRelativizationBounds SourceExistentialMap
  SourcePropositionalTemplates SourceSeparationSubset
  SourceWFFormula NumericalWFFoundation WFSubsetCore SourceWFSeparationWitness.
From Undecidability.FOL Require Import Sets.minZF Syntax.Core.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
Open Scope minZFsyn.

Lemma source_wf_domain_shift M :
  source_formula_shift M (source_wf_domain_code M)
    (code_numeral M (sf_encode (wf_class $1))).
Proof.
  pose proof (source_formula_numeral_shift M wf_domain) as H.
  assert (E:subst_form ↑ wf_domain=wf_class $1).
  { unfold wf_domain. wf_simp. reflexivity. }
  now rewrite E in H.
Qed.

Lemma source_wf_subset_shift M :
  source_formula_shift M (source_wf_subset_code M) (source_wf_subset_code M).
Proof.
  pose proof (source_formula_numeral_shift M source_wf_subset_closed) as H.
  assert (E:subst_form ↑ source_wf_subset_closed=source_wf_subset_closed).
  { unfold source_wf_subset_closed. wf_simp. reflexivity. }
  now rewrite E in H.
Qed.

Theorem source_full_WF_separation_exists M b c l n theta point profile rawex
    guardpoint guardprofile witness targetex :
  context_bounded M b c l (succM M n) ->
  source_bounded M theta (succM M (succM M (succM M n))) ->
  code_relation M (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
    (source_prop_expression separation_point_template) point ->
  sf_relation M SFAll point (zeroM M) profile ->
  sf_relation M SFEx profile (zeroM M) rawex ->
  sf_relation M SFImpl (source_wf_domain_code M) point guardpoint ->
  sf_relation M SFAll guardpoint (zeroM M) guardprofile ->
  sf_relation M SFAnd (source_wf_domain_code M) guardprofile witness ->
  sf_relation M SFEx witness (zeroM M) targetex ->
  source_full_prv M b c l (source_wf_subset_code M) ->
  source_full_prv M b c l (source_wf_domain_code M) ->
  source_full_prv M b c l rawex -> source_full_prv M b c l targetex.
Proof.
  intros HC HT HP HProfile HRawEx HG HGA HW HEx PSubset PX PRaw.
  destruct (source_sep_atom_bounds M n) as [HL HR].
  assert (HPoint:source_bounded M point (succM M (succM M (succM M n)))).
  { apply (source_prop_template_bound M
      (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
      separation_point_template (succM M (succM M (succM M n)))) with (f:=point).
    - intros [|[|i]];[exact HL|exact HR|exact HT].
    - exact HP. }
  assert (HProf:source_bounded M profile (succM M (succM M n))).
  { exact (proj2 (source_bounded_accept_unary M SFAll point profile _
      (or_introl eq_refl) HProfile) HPoint). }
  assert (HGuardProf:source_bounded M guardprofile (succM M (succM M n))).
  { apply (proj2 (source_bounded_accept_unary M SFAll guardpoint guardprofile _
      (or_introl eq_refl) HGA)).
    apply (proj2 (source_bounded_accept_binary M SFImpl (source_wf_domain_code M) point guardpoint _
      (or_intror (or_intror eq_refl)) HG)). split;[|exact HPoint].
    exact (sr_domain_bound_succ M _ (succM M (succM M n)) (numerical_wf_domain_bounded M)). }
  assert (HWit:source_bounded M witness (succM M (succM M n))).
  { apply (proj2 (source_bounded_accept_binary M SFAnd (source_wf_domain_code M) guardprofile witness _
      (or_introl eq_refl) HW)). split;[|exact HGuardProf].
    exact (sr_domain_bound_succ M _ (succM M n) (numerical_wf_domain_bounded M)). }
  assert (HExBound:source_bounded M targetex (succM M n)).
  { exact (proj2 (source_bounded_accept_unary M SFEx witness targetex _
      (or_intror eq_refl) HEx) HWit). }
  destruct (context_shift_total M b c l) as [s [t HS]].
  destruct (environment_cons_total M s t l profile) as [u [v [j HCons]]].
  destruct (numerical_renaming_total M targetex (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M))) as [shifted HShift].
  apply (source_full_exists_map M b c l profile witness rawex targetex s t u v j shifted
    (ex_intro _ (succM M n) (conj HExBound HC)) HRawEx HEx HS HCons HShift PRaw).
  assert (HCs:context_bounded M s t l (succM M (succM M n)))
    by exact (context_shift_preserves_bound M b c l s t (succM M n) HS HC).
  assert (HBranch:context_bounded M u v j (succM M (succM M n))).
  { exact (proj2 (context_bounded_cons M s t l profile u v j _ HCons) (conj HProf HCs)). }
  assert (HI:context_included M s t l u v j).
  { intros f HF. apply (proj2 (context_member_cons M s t l profile u v j f HCons)). now right. }
  assert (PS:source_full_prv M s t l (source_wf_subset_code M)).
  { exact (source_full_prv_renaming M b c l _ (zeroM M) (zeroM M) (zeroM M)
      (succM M (zeroM M)) s t _ PSubset HS (source_wf_subset_shift M)). }
  assert (PXS:source_full_prv M s t l (code_numeral M (sf_encode (wf_class $1)))).
  { exact (source_full_prv_renaming M b c l _ (zeroM M) (zeroM M) (zeroM M)
      (succM M (zeroM M)) s t _ PX HS (source_wf_domain_shift M)). }
  apply (source_full_WF_separation_witness M u v j n theta point profile guardpoint guardprofile witness
    HBranch HT HP HProfile HG HGA HW).
  - exact (source_full_prv_weaken_bounded M s t l u v j _ _ PS HI HBranch).
  - exact (source_full_prv_weaken_bounded M s t l u v j _ _ PXS HI HBranch).
  - apply (full_source_Ctx M u v j profile).
    + now exists (succM M (succM M n)).
    + apply (proj2 (context_member_cons M s t l profile u v j profile HCons)). now left.
Qed.

Print Assumptions source_wf_domain_shift.
Print Assumptions source_wf_subset_shift.
Print Assumptions source_full_WF_separation_exists.
