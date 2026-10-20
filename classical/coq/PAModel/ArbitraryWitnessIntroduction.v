(** Quantifier introduction with independently chosen internal variable
    names and quotation bases. These rules are coded proof transformations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent SetFormulaCodes
  NumericalEnvironments NumericalQuotation QuotationHygiene QuotationPayloads QuotationFunctionality
  QuotationRebase QuotedInstantiationRules ContextualProofs ContextualEquivalence
  ContextualGuardedQuantifiers ReplacementMatrixCongruence QuotedSameBaseRules QuotationSchemaSkeleton.
Unset Implicit Arguments.

Theorem contextual_quoted_all_arbitrary_introduction M cb cc cn f h
    eb ec en fb fc fn oldbase branchbase domain y all result dom db dc dn :
  sf_relation M SFAll f (zeroM M) h ->
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en y domain ->
  environment_cons M eb ec en y fb fc fn -> quotation_safe M fb fc fn branchbase domain ->
  numerical_quotation M h eb ec en oldbase domain all ->
  numerical_quotation M f fb fc fn branchbase domain result ->
  membership_graph M domain y dom -> environment_cons M cb cc cn dom db dc dn ->
  context_fresh M cb cc cn y -> contextually_provable M db dc dn result ->
  contextually_provable M cb cc cn all.
Proof.
  intros HSource HOld HY HEnv HBranch HAll HResult HDom HCtx HFresh PResult.
  destruct (numerical_quotation_total M h eb ec en y domain) as [allY HAllY].
  destruct (numerical_quotation_unary_inv M true f h eb ec en y domain allY HSource HAllY)
    as [yb [yc [yn [body [CY [HBody HQuant]]]]]].
  assert (HE : environment_equivalent M yb yc yn fb fc fn).
  { exact (environment_cons_extensional M eb ec en eb ec en y yb yc yn fb fc fn
      (fun _ _=>iff_refl _) CY HEnv). }
  assert (HBody' : numerical_quotation M f fb fc fn (succM M y) domain body).
  { exact (proj1 (numerical_quotation_environment_extensional M f yb yc yn fb fc fn
      (succM M y) domain body HE) HBody). }
  assert (HNext : quotation_safe M fb fc fn (succM M y) domain).
  { split.
    - exact (proj1 (quotation_safe_successor M eb ec en y domain HY)).
    - exact (replacement_environment_push_below M eb ec en y fb fc fn (succM M y)
        (proj2 (quotation_safe_successor M eb ec en y domain HY)) (coding_lt_succ M y) HEnv). }
  assert (PBody : contextually_provable M db dc dn body).
  { apply (contextual_equivalent_forward M db dc dn result body
      (numerical_quotation_rebase_safe M f fb fc fn branchbase (succM M y) domain
        result body HBranch HNext HResult HBody')). exact PResult. }
  assert (PAllY : contextually_provable M cb cc cn allY).
  { exact (contextual_guarded_all_intro M cb cc cn y domain body dom db dc dn allY
      HDom HCtx HFresh PBody HQuant). }
  apply (contextual_equivalent_forward M cb cc cn allY all
    (numerical_quotation_rebase_safe M h eb ec en y oldbase domain allY all HY HOld HAllY HAll)).
  exact PAllY.
Qed.

Theorem contextual_quoted_exists_arbitrary_introduction M cb cc cn f h
    eb ec en fb fc fn oldbase fresh branchbase domain y ex result dom :
  sf_relation M SFEx f (zeroM M) h ->
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en fresh domain ->
  coding_lt M y fresh -> environment_cons M eb ec en y fb fc fn ->
  quotation_safe M fb fc fn branchbase domain ->
  numerical_quotation M h eb ec en oldbase domain ex ->
  numerical_quotation M f fb fc fn branchbase domain result -> membership_graph M domain y dom ->
  contextually_provable M cb cc cn result -> contextually_provable M cb cc cn dom ->
  contextually_provable M cb cc cn ex.
Proof.
  intros HSource HOld HFresh HY HEnv HBranch HEx HResult HDom PResult PDom.
  destruct (numerical_quotation_total M h eb ec en fresh domain) as [exFresh HExFresh].
  destruct (numerical_quotation_unary_inv M false f h eb ec en fresh domain exFresh HSource HExFresh)
    as [db [dc [dn [body [HCons [HBody HQuant]]]]]].
  destruct (numerical_quotation_total M f fb fc fn (succM M fresh) domain) as [next HNext].
  assert (HSafe : quotation_safe M fb fc fn fresh domain).
  { split;[exact (proj1 HFresh)|].
    exact (replacement_environment_push_below M eb ec en y fb fc fn fresh (proj2 HFresh) HY HEnv). }
  assert (PNext : contextually_provable M cb cc cn next).
  { apply (contextual_equivalent_forward M cb cc cn result next
      (numerical_quotation_rebase_safe M f fb fc fn branchbase (succM M fresh) domain result next
        HBranch (quotation_safe_successor M fb fc fn fresh domain HSafe) HResult HNext)). exact PResult. }
  assert (PExFresh : contextually_provable M cb cc cn exFresh).
  { exact (contextual_quoted_exists_from_cons M cb cc cn f eb ec en db dc dn fb fc fn fresh domain y
      body next exFresh dom HFresh HY HCons HEnv HBody HNext HQuant HDom PNext PDom). }
  apply (contextual_equivalent_forward M cb cc cn exFresh ex
    (numerical_quotation_rebase_safe M h eb ec en fresh oldbase domain exFresh ex HFresh HOld HExFresh HEx)).
  exact PExFresh.
Qed.

Print Assumptions contextual_quoted_all_arbitrary_introduction.
Print Assumptions contextual_quoted_exists_arbitrary_introduction.

Theorem contextual_skeleton_all_arbitrary_introduction M cb cc cn s sources
    eb ec en fb fc fn oldbase branchbase domain y all result dom db dc dn :
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en y domain ->
  environment_cons M eb ec en y fb fc fn -> quotation_safe M fb fc fn branchbase domain ->
  skeleton_quotation M (SkeletonQuantifier true s) sources eb ec en oldbase domain all ->
  skeleton_quotation M s sources fb fc fn branchbase domain result ->
  membership_graph M domain y dom -> environment_cons M cb cc cn dom db dc dn ->
  context_fresh M cb cc cn y -> contextually_provable M db dc dn result ->
  contextually_provable M cb cc cn all.
Proof.
  intros HOld HY HEnv HBranch HAll HResult HDom HCtx HFresh PResult.
  destruct (code_relation_total M (skeleton_code s) sources) as [f HF].
  destruct (code_relation_total M (skeleton_code (SkeletonQuantifier true s)) sources) as [h HH].
  assert (HSource : sf_relation M SFAll f (zeroM M) h).
  { apply (proj1 (skeleton_source_relation M sources SFAll (skeleton_code s) (CEconst 0) f (zeroM M) h HF eq_refl));exact HH. }
  exact (contextual_quoted_all_arbitrary_introduction M cb cc cn f h eb ec en fb fc fn
    oldbase branchbase domain y all result dom db dc dn HSource HOld HY HEnv HBranch
    (proj1 (skeleton_quotation_correct M (SkeletonQuantifier true s) sources h HH
      eb ec en oldbase domain all) HAll)
    (proj1 (skeleton_quotation_correct M s sources f HF fb fc fn branchbase domain result) HResult)
    HDom HCtx HFresh PResult).
Qed.

Theorem contextual_skeleton_exists_arbitrary_introduction M cb cc cn s sources
    eb ec en fb fc fn oldbase fresh branchbase domain y ex result dom :
  quotation_safe M eb ec en oldbase domain -> quotation_safe M eb ec en fresh domain ->
  coding_lt M y fresh -> environment_cons M eb ec en y fb fc fn ->
  quotation_safe M fb fc fn branchbase domain ->
  skeleton_quotation M (SkeletonQuantifier false s) sources eb ec en oldbase domain ex ->
  skeleton_quotation M s sources fb fc fn branchbase domain result -> membership_graph M domain y dom ->
  contextually_provable M cb cc cn result -> contextually_provable M cb cc cn dom ->
  contextually_provable M cb cc cn ex.
Proof.
  intros HOld HFresh HY HEnv HBranch HEx HResult HDom PResult PDom.
  destruct (code_relation_total M (skeleton_code s) sources) as [f HF].
  destruct (code_relation_total M (skeleton_code (SkeletonQuantifier false s)) sources) as [h HH].
  assert (HSource : sf_relation M SFEx f (zeroM M) h).
  { apply (proj1 (skeleton_source_relation M sources SFEx (skeleton_code s) (CEconst 0) f (zeroM M) h HF eq_refl));exact HH. }
  exact (contextual_quoted_exists_arbitrary_introduction M cb cc cn f h eb ec en fb fc fn
    oldbase fresh branchbase domain y ex result dom HSource HOld HFresh HY HEnv HBranch
    (proj1 (skeleton_quotation_correct M (SkeletonQuantifier false s) sources h HH
      eb ec en oldbase domain ex) HEx)
    (proj1 (skeleton_quotation_correct M s sources f HF fb fc fn branchbase domain result) HResult)
    HDom PResult PDom).
Qed.

Print Assumptions contextual_skeleton_all_arbitrary_introduction.
Print Assumptions contextual_skeleton_exists_arbitrary_introduction.
