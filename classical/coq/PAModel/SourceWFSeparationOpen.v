(** Complete open WF Separation proof, preserving the raw schema witness. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceBoundMonotone SchemaConstructorBounds
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
  SourceProofWeakening SourceContextTransport SourceClosedContextShift SourceTraceBounds
  SourceRelativizationBounds SourceUniversalPropositional
  SourcePropositionalTemplates SourceSeparationSubset
  SourceWFFormula NumericalWFFoundation WFSubsetCore
  SourceWFSeparationWitness SourceWFSeparationExistential.
Unset Implicit Arguments.

Theorem source_full_WF_separation_open_graphs M b c l n theta point profile rawex raw
    guardpoint guardprofile witness targetex outerguard target :
  context_bounded M b c l (zeroM M) ->
  source_bounded M theta (succM M (succM M (succM M n))) ->
  code_relation M (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
    (source_prop_expression separation_point_template) point ->
  sf_relation M SFAll point (zeroM M) profile ->
  sf_relation M SFEx profile (zeroM M) rawex ->
  sf_relation M SFAll rawex (zeroM M) raw ->
  sf_relation M SFImpl (source_wf_domain_code M) point guardpoint ->
  sf_relation M SFAll guardpoint (zeroM M) guardprofile ->
  sf_relation M SFAnd (source_wf_domain_code M) guardprofile witness ->
  sf_relation M SFEx witness (zeroM M) targetex ->
  sf_relation M SFImpl (source_wf_domain_code M) targetex outerguard ->
  sf_relation M SFAll outerguard (zeroM M) target ->
  source_bounded M target n ->
  source_full_prv M b c l (source_wf_subset_code M) ->
  source_full_prv M b c l raw -> source_full_prv M b c l target.
Proof.
  intros HC HT HP HProfile HRawEx HRaw HG HGA HW HEx HOuter HTarget HBound PSubset PRaw.
  pose proof (source_closed_context_shift_self M b c l HC) as HSelf.
  assert (HCn:context_bounded M b c l n).
  { exact (context_bounded_monotone M b c l (zeroM M) n HC (coding_zero_lt_succ M n)). }
  assert (HCs:context_bounded M b c l (succM M n)).
  { exact (context_bounded_monotone M b c l (zeroM M) (succM M n) HC
      (coding_zero_lt_succ M (succM M n))). }
  pose proof (proj1 (source_bounded_accept_unary M SFAll outerguard target n
    (or_introl eq_refl) HTarget) HBound) as HOuterBound.
  apply (full_source_AllI M b c l outerguard target b c
    (ex_intro _ n (conj HBound HCn)));[|exact HSelf|exact HTarget].
  destruct (environment_cons_total M b c l (source_wf_domain_code M)) as [u [v [j HCons]]].
  assert (HBranch:context_bounded M u v j (succM M n)).
  { apply (proj2 (context_bounded_cons M b c l _ u v j _ HCons)).
    split;[exact (sr_domain_bound_succ M _ n (numerical_wf_domain_bounded M))|exact HCs]. }
  assert (HI:context_included M b c l u v j).
  { intros f HF. apply (proj2 (context_member_cons M b c l _ u v j f HCons)). now right. }
  apply (full_source_II M b c l (source_wf_domain_code M) targetex outerguard u v j
    (ex_intro _ (succM M n) (conj HOuterBound HCs)));[|exact HCons|exact HOuter].
  apply (source_full_WF_separation_exists M u v j n theta point profile rawex
    guardpoint guardprofile witness targetex HBranch HT HP HProfile HRawEx HG HGA HW HEx).
  - exact (source_full_prv_weaken_bounded M b c l u v j _ _ PSubset HI HBranch).
  - apply (full_source_Ctx M u v j (source_wf_domain_code M)).
    + exists (succM M n). split;[exact (sr_domain_bound_succ M _ n (numerical_wf_domain_bounded M))|exact HBranch].
    + apply (proj2 (context_member_cons M b c l _ u v j _ HCons)). now left.
  - exact (source_full_prv_weaken_bounded M b c l u v j _ _
      (source_full_all_shift M b c l rawex raw b c HRaw PRaw HSelf) HI HBranch).
Qed.

Print Assumptions source_full_WF_separation_open_graphs.
