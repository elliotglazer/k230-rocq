(** The collector existential is obtained from the actual raw Collection
    theorem, with an explicit numerical witness-map derivation. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeExpressions NumericalProofs NumericalVacuitySteps NumericalQuotation
  NumericalEnvironments NumericalContexts ContextualProofs ContextualWitnessRules StableContextSupport
  NamedExistential NamedBinderFresh FreshNames NamedLeibnizSteps QuotationPayloads QuotationFixedSource
  QuotationHygiene QuotationSchemaSkeleton SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  SourceBounded SupportedQuotientEnvironments RawQuotientAtomCongruence
  RawCollectionProfile RawClauseAlpha RawProfileGraphs ReplacementMatrixQuotation MatrixClauseRenaming
  BinaryMatrixFresh BinaryMatrixRenaming ContextFreshBounds ReplacementFreshAllocation
  ReplacementPointwiseSkeleton QuotedReplacementOutput ArbitraryWitnessIntroduction TemplateNamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma replacement_safe_above M eb ec en lower upper t :
  quotation_safe M eb ec en lower t -> coding_lt M lower upper -> quotation_safe M eb ec en upper t.
Proof.
  intros [HT HE] HL;split;[exact (coding_lt_trans M t lower upper HT HL)|].
  intros i value HV;exact (coding_lt_trans M value lower upper (HE i value HV) HL).
Qed.

Theorem quoted_replacement_collector_from_raw_collection M phi count ra rb rc functionSource functionQ
    eb ec en functionBase t a marker marker_name pb pc pn ab ac an base target da :
  raw_collection_template_certificates M t marker ->
  source_bounded M phi (succM M (succM M count)) ->
  schema_renaming M RepA phi ra -> schema_renaming M RepB phi rb -> schema_renaming M RepC phi rc ->
  code_relation M (ra .: rb .: fun _=>zeroM M) (E_sf_functionality (CEvar 0) (CEvar 1)) functionSource ->
  numerical_quotation M functionSource eb ec en functionBase t functionQ ->
  quotation_safe M eb ec en functionBase t -> stable_context_support M pb pc pn functionQ ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M pb pc pn marker ->
  membership_graph M t a da -> stable_context_support M pb pc pn da ->
  environment_cons M eb ec en a ab ac an -> quotation_safe M ab ac an base t ->
  skeleton_quotation M replacement_collector_skeleton (schema_env3 ra rb rc) ab ac an base t target ->
  contextually_provable M pb pc pn target.
Proof.
  intros HRaw HB RA RB RC GF FQ HF PF HM PM DA PA HA HBase HTarget.
  set (names:=cons pb (cons eb (cons a (cons t (cons target (cons (zeroM M) nil)))))).
  set (c:=replacement_name_bound M names).
  assert (Large:forall value,In value names -> coding_lt M value c).
  { intros value HV;exact (replacement_name_bound_above M names value HV). }
  assert (HpbC:coding_lt M pb c) by (apply Large;unfold names;simpl;tauto).
  assert (HebC:coding_lt M eb c) by (apply Large;unfold names;simpl;tauto).
  assert (HaC:coding_lt M a c) by (apply Large;unfold names;simpl;tauto).
  assert (HtC:coding_lt M t c) by (apply Large;unfold names;simpl;tauto).
  assert (HtargetC:coding_lt M target c) by (apply Large;unfold names;simpl;tauto).
  assert (H0C:coding_lt M (zeroM M) c) by (apply Large;unfold names;simpl;tauto).
  set (u:=succM M c). set (v:=succM M u). set (k:=succM M v).
  assert (HCU:coding_lt M c u) by apply coding_lt_succ.
  assert (HUV:coding_lt M u v) by apply coding_lt_succ.
  assert (HVK:coding_lt M v k) by apply coding_lt_succ.
  assert (HCV:coding_lt M c v) by exact (coding_lt_trans M c u v HCU HUV).
  assert (HUK:coding_lt M u k) by exact (coding_lt_trans M u v k HUV HVK).
  assert (HCK:coding_lt M c k) by exact (coding_lt_trans M c v k HCV HVK).
  assert (HRootC:quotation_safe M eb ec en c t).
  { split;[exact HtC|exact (environment_below_above_code M eb ec en c HebC H0C)]. }
  assert (HRootK:quotation_safe M eb ec en k t) by exact (replacement_safe_above M eb ec en c k t HRootC HCK).
  assert (HUC:u<>c) by exact (template_lt_different M c u HCU).
  assert (HVC:v<>c) by exact (template_lt_different M c v HCV).
  assert (HUN:u<>zeroM M) by exact (template_lt_different M (zeroM M) u (coding_lt_trans M (zeroM M) c u H0C HCU)).
  assert (HVN:v<>zeroM M) by exact (template_lt_different M (zeroM M) v (coding_lt_trans M (zeroM M) c v H0C HCV)).
  assert (HCN:c<>zeroM M) by exact (template_lt_different M (zeroM M) c H0C).
  assert (EC:environment_avoids_name M eb ec en c).
  { exact (environment_avoids_above_code M eb ec en c HebC HCN). }
  assert (EU:environment_avoids_name M eb ec en u).
  { exact (environment_avoids_above_code M eb ec en u (coding_lt_trans M eb c u HebC HCU) HUN). }
  assert (EV:environment_avoids_name M eb ec en v).
  { exact (environment_avoids_above_code M eb ec en v (coding_lt_trans M eb c v HebC HCV) HVN). }
  assert (NU:raw_clause_usable_name M eb ec en t a c k u).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t u (coding_lt_trans M t c u HtC HCU) (eq_sym E)).
    - exact (fun E=>template_lt_different M a u (coding_lt_trans M a c u HaC HCU) (eq_sym E)).
    - exact (fun E=>template_lt_different M c u HCU (eq_sym E)). }
  assert (NV:raw_clause_usable_name M eb ec en t a c k v).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t v (coding_lt_trans M t c v HtC HCV) (eq_sym E)).
    - exact (fun E=>template_lt_different M a v (coding_lt_trans M a c v HaC HCV) (eq_sym E)).
    - exact (fun E=>template_lt_different M c v HCV (eq_sym E)). }
  assert (UV:u<>v) by exact (fun E=>template_lt_different M u v HUV (eq_sym E)).
  destruct (binary_matrix_total M phi eb ec en u v k t) as [theta QT].
  assert (FTC:formula_fresh M theta c) by exact (binary_matrix_formula_fresh M phi eb ec en u v k t theta c
    QT HCK HCN (template_lt_different M t c HtC) HUC HVC EC).
  assert (BAU:named_binder_absent M theta u) by exact (binary_matrix_binder_absent M phi eb ec en u v k t theta u QT HUK).
  assert (BAV:named_binder_absent M theta v) by exact (binary_matrix_binder_absent M phi eb ec en u v k t theta v QT HVK).
  set (rho:=raw_clause_parameters M t a c u v theta).
  set (PExpr:=E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)).
  destruct (code_relation_total M PExpr rho) as [profile GP].
  destruct (code_relation_total M (E_wex (CEvar 2) PExpr) rho) as [exraw GEx].
  destruct (code_relation_total M (E_raw_collection_statement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) rho) as [statement GStatement].

  assert (PStatement:stable_context_support M pb pc pn statement).
  { apply (stable_context_support_implies M pb pc pn marker statement);[|exact PM].
    destruct NU as [_ [TU [AU [CU _]]]],NV as [_ [TV [AV [CV _]]]].
    exact (HRaw a c u v theta HCN HUN HVN
      (fun E=>template_lt_different M t c HtC (eq_sym E)) TU TV
      (fun E=>template_lt_different M a c HaC (eq_sym E)) AU AV CU CV UV FTC BAU BAV statement GStatement). }
  assert (GDA:code_relation M rho (E_wel (CEvar 0) (CEvar 1)) da).
  { exact (proj2 (ns_atom_expression M rho false (CEvar 0) (CEvar 1) t a da eq_refl eq_refl) DA). }
  assert (GImp:implication_graph M da exraw statement).
  { exact (proj1 (expression_implication_iff M rho (E_wel (CEvar 0) (CEvar 1))
      (E_wex (CEvar 2) PExpr) da exraw statement GDA GEx) GStatement). }
  assert (PEx:contextually_provable M pb pc pn exraw).
  { apply stable_context_support_here;exact (stable_context_support_mp M pb pc pn da exraw statement GImp PA PStatement). }
  assert (GExRaw:named_exists_graph M c profile exraw).
  { exact (proj1 (named_exists_expression M rho (CEvar 2) PExpr c profile exraw eq_refl GP) GEx). }
  destruct (environment_cons_total M ab ac an c) as [cb [cc [cn HC]]].
  assert (HInputK:quotation_safe M ab ac an k t).
  { exact (replacement_safe_cons M eb ec en a ab ac an k t HRootK
      (coding_lt_trans M a c k HaC HCK) HA). }
  assert (HCollectionK:quotation_safe M cb cc cn k t).
  { exact (replacement_safe_cons M ab ac an c cb cc cn k t HInputK HCK HC). }
  destruct (skeleton_quotation_total M replacement_output_skeleton (schema_env3 ra rb rc) cb cc cn k t)
    as [allout HAllOut].
  destruct (environment_cons_total M pb pc pn profile) as [db [dc [dn HProfile]]].
  apply (contextual_witness_bind M pb pc pn c profile exraw target db dc dn
    (context_fresh_above_code M pb pc pn c HpbC) (formula_above_is_fresh M target c HtargetC)
    GExRaw HProfile PEx).
  assert (PProfile:stable_context_support M db dc dn profile).
  { apply stable_context_support_member;apply (proj2 (context_member_cons M pb pc pn profile db dc dn profile HProfile));now left. }
  assert (PAllOut:contextually_provable M db dc dn allout).
  { exact (quoted_replacement_output_from_profile M phi count ra rb rc functionSource functionQ
      eb ec en functionBase k t a c u v theta profile marker marker_name db dc dn
      ab ac an cb cc cn k allout HB RA RB RC GF FQ HF
      (stable_context_support_cons M pb pc pn profile db dc dn functionQ HProfile PF)
      HM (stable_context_support_cons M pb pc pn profile db dc dn marker HProfile PM)
      NU NV UV HRootK QT GP PProfile HA HC HCollectionK HAllOut). }
  destruct (raw_profile_parts_of_code M t a c u v theta profile GP)
    as (domC & cov & supp & allcov & allsupp & both & Parts).
  pose proof (stable_raw_profile_parts M db dc dn t a c u v theta profile domC cov supp allcov allsupp both Parts PProfile)
    as [PDom _].
  destruct Parts as [GDom _].
  exact (contextual_skeleton_exists_arbitrary_introduction M db dc dn replacement_output_skeleton
    (schema_env3 ra rb rc) ab ac an cb cc cn base k k t c target allout domC
    HBase HInputK HCK HC HCollectionK HTarget HAllOut GDom PAllOut
    (stable_context_support_here M db dc dn domC PDom)).
Qed.

Print Assumptions replacement_safe_above.
Print Assumptions quoted_replacement_collector_from_raw_collection.

