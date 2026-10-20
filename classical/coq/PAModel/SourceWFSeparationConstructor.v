(** Exact constructor alignment for the open WF Separation proof. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SchemaConstructorBounds SourceNumeralLift
  NumericalContexts NumericalSourceFull SourceRelativizationBounds QuotationSchemaSkeleton
  SourceSchemaRelativization SourceRelativeSchemaConstructors
  SourcePropositionalTemplates SourcePropositionalRebase SourceSeparationPropositional
  SourceSeparationSubset SourceWFFormula NumericalWFFoundation WFSubsetCore
  SourceWFSeparationWitness SourceWFSeparationOpen.
Unset Implicit Arguments.

Lemma schema_expression_quantifier_split M env h A f :
  code_relation M env (E_sf h A (CEconst 0)) f ->
  exists a,code_relation M env A a /\sf_relation M h a (zeroM M) f.
Proof.
  intro H. destruct (schema_expression_split M env h A (CEconst 0) f H)
    as [a [z [HA [HZ HF]]]]. change (z=zeroM M) in HZ. subst z. now exists a.
Qed.

Lemma source_sep_point_graph M env i theta point : env i=theta ->
  (code_relation M env (E_sf_iff (E_sf_mem 0 1) (E_sf SFAnd (E_sf_mem 0 2) (CEvar i))) point <->
   code_relation M (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
     (source_prop_expression separation_point_template) point).
Proof.
  intro E. apply (source_prop_expression_with_graph M env
    (fun j=>match j with 0=>E_sf_mem 0 1|1=>E_sf_mem 0 2|_=>CEvar i end)
    (schema_env3 (source_sep_left_code M) (source_sep_right_code M) theta)
    separation_point_template).
  intros [|[|j]];cbn [schema_env3].
  - apply (proj2 (schema_expression_graph M env SFMember (CEconst 0) (CEconst 1)
      (code_numeral M 0) (code_numeral M 1) (source_sep_left_code M) eq_refl eq_refl)).
    exact (sf_make_numeral M SFMember 0 1).
  - apply (proj2 (schema_expression_graph M env SFMember (CEconst 0) (CEconst 2)
      (code_numeral M 0) (code_numeral M 2) (source_sep_right_code M) eq_refl eq_refl)).
    exact (sf_make_numeral M SFMember 0 2).
  - change (theta=env i). now symmetry.
Qed.

Lemma source_relative_separation_bound M domain theta f n :
  source_bounded M domain (code_numeral M 1) ->
  source_bounded M theta (succM M (succM M (succM M n))) ->
  sf_relative_separation_constructor M domain theta f ->source_bounded M f n.
Proof.
  intros HD HT HF. unfold sf_relative_separation_constructor in HF.
  rewrite relative_separation_skeleton_exact in HF.
  assert (HB:schema_expression_bound M (skeleton_relative_environment domain (fun _=>theta))
    (E_sf_relative_separation (CEvar 0) (CEvar 1)) n).
  { unfold E_sf_relative_separation,E_sf_relative_all,E_sf_relative_ex,E_sf_all,E_sf_ex,E_sf_mem.
    repeat schema_constructor_bound;try schema_small_index;
      cbn [skeleton_relative_environment];try exact HT;
      apply sr_domain_bound_succ;exact HD. }
  exact (HB f HF).
Qed.

Local Opaque source_wf_domain_code source_sep_left_code source_sep_right_code source_wf_subset_code.

Theorem source_full_WF_separation_open M b c l n theta raw target :
  context_bounded M b c l (zeroM M) ->
  source_bounded M theta (succM M (succM M (succM M n))) ->
  sf_separation_constructor M theta raw ->
  sf_relative_separation_constructor M (source_wf_domain_code M) theta target ->
  source_full_prv M b c l (source_wf_subset_code M) ->
  source_full_prv M b c l raw ->source_full_prv M b c l target.
Proof.
  intros HC HT HRaw HTarget PS PR.
  pose proof (source_relative_separation_bound M _ theta target n
    (numerical_wf_domain_bounded M) HT HTarget) as HBound.
  unfold sf_separation_constructor,E_sf_separation,E_sf_all,E_sf_ex in HRaw.
  destruct (schema_expression_quantifier_split M _ SFAll _ raw HRaw)
    as [rawex [HRawEx HRawAll]].
  destruct (schema_expression_quantifier_split M _ SFEx _ rawex HRawEx)
    as [profile [HProfile HRawExists]].
  destruct (schema_expression_quantifier_split M _ SFAll _ profile HProfile)
    as [point [HPoint HProfileAll]].
  apply (proj1 (source_sep_point_graph M (fun _=>theta) 0 theta point eq_refl)) in HPoint.
  unfold sf_relative_separation_constructor in HTarget.
  rewrite relative_separation_skeleton_exact in HTarget.
  cbn [E_sf_relative_separation E_sf_relative_all E_sf_relative_ex E_sf_all E_sf_ex] in HTarget.
  destruct (schema_expression_quantifier_split M _ SFAll _ target HTarget)
    as [outerguard [HOuterGuard HTargetAll]].
  destruct (schema_expression_split M _ SFImpl _ _ outerguard HOuterGuard)
    as [d [targetex [HD [HTargetEx HOuter]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  destruct (schema_expression_quantifier_split M _ SFEx _ targetex HTargetEx)
    as [witness [HWitness HTargetExists]].
  destruct (schema_expression_split M _ SFAnd _ _ witness HWitness)
    as [d [guardprofile [HD [HGuardProfile HWitnessAnd]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  destruct (schema_expression_quantifier_split M _ SFAll _ guardprofile HGuardProfile)
    as [guardpoint [HGuardPoint HGuardProfileAll]].
  destruct (schema_expression_split M _ SFImpl _ _ guardpoint HGuardPoint)
    as [d [point' [HD [HPoint' HGuardPointImpl]]]].
  change (d=source_wf_domain_code M) in HD. subst d.
  apply (proj1 (source_sep_point_graph M _ 1 theta point' eq_refl)) in HPoint'.
  pose proof (code_relation_functional M (source_prop_expression separation_point_template)
    _ point point' HPoint HPoint') as E. subst point'.
  exact (source_full_WF_separation_open_graphs M b c l n theta point profile rawex raw
    guardpoint guardprofile witness targetex outerguard target HC HT HPoint HProfileAll
    HRawExists HRawAll HGuardPointImpl HGuardProfileAll HWitnessAnd HTargetExists
    HOuter HTargetAll HBound PS PR).
Qed.

Print Assumptions source_sep_point_graph.
Print Assumptions source_relative_separation_bound.
Print Assumptions source_full_WF_separation_open.
