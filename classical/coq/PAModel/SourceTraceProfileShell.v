(** Trace profiles over arbitrary model-valued container names. This is
    needed after source AllI/ExE has shifted the ambient variables. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetSchemaConstructors NumericalContexts NumericalSourceFull
  SourceTracePointRules SourcePropositionalTemplates SourceSeparationSubset
  SourcePropositionalSubstitution SourcePropositionalRebase NumericalRenaming
  NumericalRenamingMaps NumericalContextRenaming NumericalSubstitutionMaps RenamingSubstitution
  SourceQuantifierRules SourceInstantiationConstructors SourceConjunctionRules
  SourceDerivedRules SourceSequents SourceBounded NumericalInstantiation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_trace_profile_shell M theta c b profile := exists left right point,
  sf_relation M SFMember (zeroM M) (succM M c) left /\
  sf_relation M SFMember (zeroM M) (succM M b) right /\
  code_relation M (schema_env3 left right theta)
    (source_prop_expression separation_point_template) point /\
  sf_relation M SFAll point (zeroM M) profile.
Definition source_trace_profile_shell_formula (theta c b profile:term) :form :=
  ∃∃∃ (sf_formula SFMember zero (σ (lift3 c)) $2 ∧
    (sf_formula SFMember zero (σ (lift3 b)) $1 ∧
    (code_formula (source_prop_expression separation_point_template)
      (schema_env3 $2 $1 (lift3 theta)) $0 ∧
    sf_formula SFAll $0 zero (lift3 profile)))).
Local Opaque holds sf_formula code_formula.

Theorem source_trace_profile_shell_formula_correct M rho theta c b profile :
  holds M rho (source_trace_profile_shell_formula theta c b profile) <->
  source_trace_profile_shell M (evalM M rho theta) (evalM M rho c)
    (evalM M rho b) (evalM M rho profile).
Proof.
  unfold source_trace_profile_shell_formula,source_trace_profile_shell.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. setoid_rewrite code_formula_correct.
  repeat setoid_rewrite substitution_map_eval_succ.
  unfold schema_env3,evalM,lift3. repeat setoid_rewrite eval_up.
  split;intros (l&r&p&HL&HR&HP&HAll);exists l,r,p;repeat split;try assumption.
  all: refine (proj1 (code_relation_ext M _ _ _ _ _) HP);intros [|[|i]];cbn;repeat rewrite eval_up;reflexivity.
Qed.

Theorem source_trace_profile_shell_total M theta c b :
  exists profile,source_trace_profile_shell M theta c b profile.
Proof.
  destruct (sf_relation_total M SFMember (zeroM M) (succM M c)) as [left HL].
  destruct (sf_relation_total M SFMember (zeroM M) (succM M b)) as [right HR].
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left right theta)) as [point HP].
  destruct (sf_relation_total M SFAll point (zeroM M)) as [profile HAll].
  exists profile,left,right,point. auto.
Qed.

Theorem source_prop_expression_renaming M rho rho' rb rc rn delta a f g :
  (forall i,numerical_renaming M (rho i) rb rc rn delta (rho' i)) ->
  code_relation M rho (source_prop_expression a) f ->
  code_relation M rho' (source_prop_expression a) g ->
  numerical_renaming M f rb rc rn delta g.
Proof.
  intros HH HF HG. apply (proj2 (numerical_renaming_substitution M f rb rc rn delta g)).
  apply (source_prop_expression_substitution M rho rho' rb rc rn (addM M rn delta) a);
    [|exact HF|exact HG].
  intro i. exact (proj1 (numerical_renaming_substitution M (rho i) rb rc rn delta (rho' i)) (HH i)).
Qed.

Theorem source_trace_profile_shell_shift M theta c b profile shifted :
  source_trace_profile_shell M theta c b profile -> source_formula_shift M profile shifted ->
  exists theta' rb rc rn,
    renaming_lift M (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) rb rc rn /\
    numerical_renaming M theta rb rc rn (code_numeral M 1) theta' /\
    source_trace_profile_shell M theta' (succM M c) (succM M b) shifted.
Proof.
  intros [left [right [point [HL [HR [HP HAll]]]]]] HS.
  destruct (proj1 (numerical_renaming_quantifier M true point profile
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) shifted HAll) HS)
    as [rb [rc [rn [p' [HLift [HPoint HAll']]]]]].
  destruct (numerical_renaming_total M theta rb rc rn (code_numeral M 1)) as [theta' HT].
  destruct (sf_relation_total M SFMember (zeroM M) (succM M (succM M c))) as [left' HL'].
  destruct (sf_relation_total M SFMember (zeroM M) (succM M (succM M b))) as [right' HR'].
  assert (RLeft:numerical_renaming M left rb rc rn (code_numeral M 1) left').
  { apply (proj2 (numerical_renaming_member M (zeroM M) (succM M c) left
      rb rc rn (code_numeral M 1) left' HL)).
    exists (zeroM M),(succM M (succM M c)). split.
    - exact (proj2 (renaming_lift_head M _ _ _ _ rb rc rn (zeroM M) HLift) eq_refl).
    - split;[|exact HL'].
      apply (proj2 (renaming_lift_tail M _ _ _ _ rb rc rn c (succM M c) HLift)).
      apply context_shift_lookup. reflexivity. }
  assert (RRight:numerical_renaming M right rb rc rn (code_numeral M 1) right').
  { apply (proj2 (numerical_renaming_member M (zeroM M) (succM M b) right
      rb rc rn (code_numeral M 1) right' HR)).
    exists (zeroM M),(succM M (succM M b)). split.
    - exact (proj2 (renaming_lift_head M _ _ _ _ rb rc rn (zeroM M) HLift) eq_refl).
    - split;[|exact HR'].
      apply (proj2 (renaming_lift_tail M _ _ _ _ rb rc rn b (succM M b) HLift)).
      apply context_shift_lookup. reflexivity. }
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left' right' theta')) as [target HTarget].
  assert (RT:numerical_renaming M point rb rc rn (code_numeral M 1) target).
  { apply (source_prop_expression_renaming M (schema_env3 left right theta)
      (schema_env3 left' right' theta') rb rc rn (code_numeral M 1)
      separation_point_template point target);[|exact HP|exact HTarget].
    intros [|[|i]];cbn [schema_env3];assumption. }
  pose proof (numerical_renaming_functional M point rb rc rn (code_numeral M 1)
    p' target HPoint RT) as E. subst target.
  exists theta',rb,rc,rn. split;[exact HLift|]. split;[exact HT|].
  exists left',right',p'. auto.
Qed.

Theorem source_full_trace_shell_point M cb cc cn theta c b profile x left right some point :
  source_trace_profile_shell M theta c b profile ->
  sf_relation M SFMember x c left -> sf_relation M SFMember x b right ->
  numerical_instantiation M theta x some ->
  code_relation M (schema_env3 left right some)
    (source_prop_expression separation_point_template) point ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn point.
Proof.
  intros [l [r [body [HL [HR [HB HAll]]]]]] HLeft HRight HSome HPoint PP.
  assert (HI:numerical_instantiation M body x point).
  { apply (source_prop_expression_instantiation M (schema_env3 l r theta)
      (schema_env3 left right some) x separation_point_template body point);[|exact HB|exact HPoint].
    intros [|[|i]];cbn [schema_env3].
    - exact (source_instantiation_head_member M c l x left HL HLeft).
    - exact (source_instantiation_head_member M b r x right HR HRight).
    - exact HSome. }
  apply (full_source_AllE M cb cc cn body profile x point).
  - exact (source_wf_quantifier_instance M cb cc cn SFAll body profile x point
      (or_introl eq_refl) HAll (source_full_prv_wellformed M cb cc cn profile PP) HI).
  - exact PP.
  - exact HAll.
  - exact HI.
Qed.

Theorem source_full_trace_shell_parent M cb cc cn theta c b profile x left right :
  source_trace_profile_shell M theta c b profile ->
  sf_relation M SFMember x c left -> sf_relation M SFMember x b right ->
  source_full_prv M cb cc cn profile -> source_full_prv M cb cc cn left ->
  source_full_prv M cb cc cn right.
Proof.
  intros HProfile HL HR PP PL.
  destruct (numerical_instantiation_total M theta x) as [some HS].
  destruct (code_relation_total M (source_prop_expression separation_point_template)
    (schema_env3 left right some)) as [point HPoint].
  pose proof (source_full_trace_shell_point M cb cc cn theta c b profile x left right some point
    HProfile HL HR HS HPoint PP) as PPoint.
  destruct (source_trace_point_unpack M left right some point HPoint)
    as [rhs [forward [reverse [HAnd [HF [HV HI]]]]]].
  pose proof (source_full_conjunction_left M cb cc cn forward reverse point HI PPoint) as PF.
  pose proof (source_full_modus_ponens M cb cc cn left rhs forward HF PF PL) as PRhs.
  exact (source_full_conjunction_left M cb cc cn right some rhs HAnd PRhs).
Qed.

Print Assumptions source_trace_profile_shell_formula_correct.
Print Assumptions source_trace_profile_shell_total.
Print Assumptions source_prop_expression_renaming.
Print Assumptions source_trace_profile_shell_shift.
Print Assumptions source_full_trace_shell_point.
Print Assumptions source_full_trace_shell_parent.
