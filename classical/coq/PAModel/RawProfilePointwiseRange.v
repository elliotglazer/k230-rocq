(** Both directions of the quotient image condition, as a stable numerical
    proof under the actual raw Collection profile and source functionality. *)
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs NumericalQuotation
  NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts ContextualProofs
  ContextualDeduction ContextualPropositional StableContextSupport
  SourceBounded SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  QuotationPayloads QuotationHygiene SupportedQuotientEnvironments RawQuotientAtomCongruence
  RawCollectionProfile RawClauseAlpha ReplacementMatrixQuotation MatrixClauseRenaming HybridImageGraphs
  FreshProfileSupport FreshProfileCoverage.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem raw_profile_pointwise_range_equivalence M phi count ra rb functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name cb cc cn
    x y atomBase matrixBase image qbase q dy forward backward equivalence :
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  numerical_quotation M functionSource eb ec en functionBase t functionQ ->
  quotation_safe M eb ec en functionBase t -> stable_context_support M cb cc cn functionQ ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  raw_clause_usable_name M eb ec en t a c profileBase u0 ->
  raw_clause_usable_name M eb ec en t a c profileBase v0 -> u0<>v0 ->
  quotation_safe M eb ec en profileBase t ->
  binary_matrix_quotation M phi eb ec en u0 v0 profileBase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M cb cc cn profile ->
  quotation_safe M eb ec en x t -> coding_lt M a x -> coding_lt M y x ->
  quotient_pair_safe M t x a atomBase -> quotation_safe M eb ec en matrixBase t ->
  coding_lt M x matrixBase -> coding_lt M y matrixBase ->
  hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase image ->
  membership_graph M t y dy -> stable_context_support M cb cc cn dy ->
  quotient_pair_safe M t y c qbase -> quotation_atom M false y c t qbase q ->
  implication_graph M q image forward -> implication_graph M image q backward ->
  quotation_binary M SFAnd forward backward equivalence ->
  stable_context_support M cb cc cn equivalence.
Proof.
  intros HB RA RB GF FQ HF PF HM PM NU0 NV0 HUV HP Q0 GP PP HX HAX HYX
    HAB HMB HXM HYM Image DY PY HQ GQ GFor GBack GE.
  intros db dc dn Incl.
  destruct (environment_cons_total M db dc dn q) as [qb [qc [qn CQ]]].
  assert (QIncl:context_included M cb cc cn qb qc qn).
  { apply (context_included_trans M cb cc cn db dc dn qb qc qn Incl).
    intros f H;apply (proj2 (context_member_cons M db dc dn q qb qc qn f CQ));now right. }
  assert (PQ:contextually_provable M qb qc qn q).
  { apply contextual_hyp;apply (proj2 (context_member_cons M db dc dn q qb qc qn q CQ));now left. }
  assert (PI:contextually_provable M qb qc qn image).
  { exact (raw_profile_implies_quotient_image M phi count eb ec en profileBase t a c u0 v0 theta0 profile
      marker marker_name qb qc qn y qbase q x atomBase matrixBase image
      HB HM (stable_context_support_included M cb cc cn qb qc qn marker QIncl PM)
      NU0 NV0 HUV HP Q0 GP (stable_context_support_included M cb cc cn qb qc qn profile QIncl PP)
      HQ GQ PQ HX HAX HYX HAB HMB HXM HYM Image). }
  destruct (contextual_deduction M db dc dn q qb qc qn image CQ PI) as [f [GF' PF']].
  assert (EF:f=forward) by exact (code_relation_functional M (E_wim (CEvar 0) (CEvar 1)) (q .: image .: fun _=>zeroM M) f forward GF' GFor).
  subst f.
  destruct (environment_cons_total M db dc dn image) as [ib [ic [ine CI]]].
  assert (IIncl:context_included M cb cc cn ib ic ine).
  { apply (context_included_trans M cb cc cn db dc dn ib ic ine Incl).
    intros f H;apply (proj2 (context_member_cons M db dc dn image ib ic ine f CI));now right. }
  assert (PI':contextually_provable M ib ic ine image).
  { apply contextual_hyp;apply (proj2 (context_member_cons M db dc dn image ib ic ine image CI));now left. }
  assert (PQ':contextually_provable M ib ic ine q).
  { exact (raw_profile_quotient_image_implies_membership M phi count ra rb functionSource functionQ
      eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name ib ic ine
      x y atomBase matrixBase image qbase q dy
      HB RA RB GF FQ HF (stable_context_support_included M cb cc cn ib ic ine functionQ IIncl PF)
      HM (stable_context_support_included M cb cc cn ib ic ine marker IIncl PM)
      NU0 NV0 HUV HP Q0 GP (stable_context_support_included M cb cc cn ib ic ine profile IIncl PP)
      HX HAX HYX HAB HMB HXM HYM Image DY (stable_context_support_included M cb cc cn ib ic ine dy IIncl PY)
      HQ GQ PI'). }
  destruct (contextual_deduction M db dc dn image ib ic ine q CI PQ') as [f [GG PB']].
  assert (EF:f=backward) by exact (code_relation_functional M (E_wim (CEvar 0) (CEvar 1)) (image .: q .: fun _=>zeroM M) f backward GG GBack).
  subst f.
  exact (contextual_conjunction_intro M db dc dn forward backward equivalence PF' PB' GE).
Qed.

Print Assumptions raw_profile_pointwise_range_equivalence.


