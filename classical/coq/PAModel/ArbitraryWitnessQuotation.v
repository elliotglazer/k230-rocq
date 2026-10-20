(** Specialization at an arbitrary model-valued witness. The witness need
    not be named by a term in the old parameter environment. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions CodeDescent
  SetFormulaCodes NumericalEnvironments NumericalQuotation QuotationHygiene NamedLeibnizSteps
  QuotationFunctionality QuotationRebase QuotedSameBaseRules QuotedInstantiationRules
  ContextualProofs StableContextSupport ReplacementMatrixCongruence
  QuotationSchemaSkeleton.
Unset Implicit Arguments.

Theorem contextual_quoted_all_arbitrary_witness M cb cc cn f h
    eb ec en fb fc fn oldbase fresh domain y all result dom :
  quotation_safe M eb ec en oldbase domain ->
  quotation_safe M eb ec en fresh domain -> coding_lt M y fresh ->
  sf_relation M SFAll f (zeroM M) h ->
  environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M h eb ec en oldbase domain all ->
  numerical_quotation M f fb fc fn fresh domain result ->
  membership_graph M domain y dom ->
  contextually_provable M cb cc cn all -> contextually_provable M cb cc cn dom ->
  contextually_provable M cb cc cn result.
Proof.
  intros HOld HFresh HY HSource HEnv HAll HResult HDom PAll PDom.
  destruct (numerical_quotation_total M h eb ec en fresh domain) as [all' HAll'].
  assert (PAll' : contextually_provable M cb cc cn all').
  { apply (contextual_equivalent_forward M cb cc cn all all'
      (numerical_quotation_rebase_safe M h eb ec en oldbase fresh domain
        all all' HOld HFresh HAll HAll')). exact PAll. }
  destruct (numerical_quotation_unary_inv M true f h eb ec en fresh domain all'
      HSource HAll') as [db [dc [dn [body [HCons [HBody HQuant]]]]]].
  destruct (numerical_quotation_total M f fb fc fn (succM M fresh) domain) as [next HNext].
  assert (HSafe : quotation_safe M fb fc fn fresh domain).
  { split;[exact (proj1 HFresh)|].
    exact (replacement_environment_push_below M eb ec en y fb fc fn fresh
      (proj2 HFresh) HY HEnv). }
  apply (contextual_equivalent_forward M cb cc cn next result
    (numerical_quotation_rebase_safe M f fb fc fn (succM M fresh) fresh domain
      next result (quotation_safe_successor M fb fc fn fresh domain HSafe)
      HSafe HNext HResult)).
  exact (contextual_quoted_all_from_cons M cb cc cn f eb ec en db dc dn fb fc fn
    fresh domain y body next all' dom HFresh HY HCons HEnv HBody HNext
    HQuant HDom PAll' PDom).
Qed.

Theorem stable_quoted_all_arbitrary_witness M cb cc cn f h
    eb ec en fb fc fn oldbase fresh domain y all result dom :
  quotation_safe M eb ec en oldbase domain ->
  quotation_safe M eb ec en fresh domain -> coding_lt M y fresh ->
  sf_relation M SFAll f (zeroM M) h ->
  environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M h eb ec en oldbase domain all ->
  numerical_quotation M f fb fc fn fresh domain result ->
  membership_graph M domain y dom ->
  stable_context_support M cb cc cn all -> stable_context_support M cb cc cn dom ->
  stable_context_support M cb cc cn result.
Proof.
  intros HOld HFresh HY HSource HEnv HAll HResult HDom PAll PDom db dc dn HI.
  exact (contextual_quoted_all_arbitrary_witness M db dc dn f h
    eb ec en fb fc fn oldbase fresh domain y all result dom
    HOld HFresh HY HSource HEnv HAll HResult HDom
    (PAll db dc dn HI) (PDom db dc dn HI)).
Qed.

Lemma skeleton_quotation_total M s sources eb ec en fresh domain :
  exists result, skeleton_quotation M s sources eb ec en fresh domain result.
Proof.
  destruct (code_relation_total M (skeleton_code s) sources) as [f HF].
  destruct (numerical_quotation_total M f eb ec en fresh domain) as [result HR].
  exists result. exact (proj2 (skeleton_quotation_correct M s sources f HF
    eb ec en fresh domain result) HR).
Qed.

Theorem stable_skeleton_all_arbitrary_witness M cb cc cn s sources
    eb ec en fb fc fn oldbase fresh domain y all result dom :
  quotation_safe M eb ec en oldbase domain ->
  quotation_safe M eb ec en fresh domain -> coding_lt M y fresh ->
  environment_cons M eb ec en y fb fc fn ->
  skeleton_quotation M (SkeletonQuantifier true s) sources eb ec en oldbase domain all ->
  skeleton_quotation M s sources fb fc fn fresh domain result ->
  membership_graph M domain y dom ->
  stable_context_support M cb cc cn all -> stable_context_support M cb cc cn dom ->
  stable_context_support M cb cc cn result.
Proof.
  intros HOld HFresh HY HEnv HAll HResult HDom PAll PDom.
  destruct (code_relation_total M (skeleton_code s) sources) as [f HF].
  destruct (code_relation_total M (skeleton_code (SkeletonQuantifier true s)) sources) as [h HH].
  assert (HSource : sf_relation M SFAll f (zeroM M) h).
  { apply (proj1 (skeleton_source_relation M sources SFAll (skeleton_code s)
      (CEconst 0) f (zeroM M) h HF eq_refl)). exact HH. }
  exact (stable_quoted_all_arbitrary_witness M cb cc cn f h
    eb ec en fb fc fn oldbase fresh domain y all result dom HOld HFresh HY
    HSource HEnv
    (proj1 (skeleton_quotation_correct M (SkeletonQuantifier true s) sources h HH
      eb ec en oldbase domain all) HAll)
    (proj1 (skeleton_quotation_correct M s sources f HF
      fb fc fn fresh domain result) HResult) HDom PAll PDom).
Qed.

Print Assumptions contextual_quoted_all_arbitrary_witness.
Print Assumptions stable_quoted_all_arbitrary_witness.
Print Assumptions skeleton_quotation_total.
Print Assumptions stable_skeleton_all_arbitrary_witness.
