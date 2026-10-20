(** Raw Collection coverage gives the reverse quotient-image implication.
    The only logical assumptions are the original raw profile and the
    exact source functionality; all clause and witness hygiene is derived. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeTags CodeExpressions
  NumericalProofs NumericalQuotation NumericalEquivalence NumericalVacuitySteps NumericalEnvironments NumericalContexts
  ContextualProofs ContextualDeduction ContextualWitnessRules StableContextSupport
  NamedExistential NamedBinderFresh FreshNames NamedLeibnizSteps FormulaFreshConstructors
  SourceBounded SetFormulaCodes SetSchemaConstructors SchemaRenamingDescriptors
  QuotationPayloads QuotationFixedSource QuotationHygiene QuotationAtomRebase QuotationFormulaFresh
  TemplateFormulaFresh TemplateNamedSubstitution ContextualGuardedQuantifiers
  SupportedQuotientEnvironments RawQuotientAtomCongruence ReplacementMatrixQuotation
  RawDmemWitness RawCollectionProfile RawClauseAlpha RawClauseHygiene RawClauseGraphs
  MatrixClauseRenaming ProfileRebasedClauses BinaryMatrixFresh BinaryMatrixRenaming
  ActualCollectionCoverage QuotientInputCoverage CollectionWitnessKernels
  ContextFreshBounds QuotedSameBaseRules SubstitutionEnvironmentTotal.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma raw_image_body_fresh M t x dom q theta rest body name :
  membership_graph M t x dom -> quotation_binary M SFAnd q theta rest ->
  quotation_binary M SFAnd dom rest body ->
  name<>zeroM M -> t<>name -> x<>name -> formula_fresh M q name -> formula_fresh M theta name ->
  formula_fresh M body name.
Proof.
  intros GD GR GB H0 HT HX HQ HP.
  apply (quotation_binary_fresh M SFAnd dom rest body name GB H0).
  - exact (formula_fresh_membership_intro M t x dom name GD HT HX).
  - exact (quotation_binary_fresh M SFAnd q theta rest name GR H0 HQ HP).
Qed.

Theorem profile_coverage_at_fresh_witnesses M phi count ra rb functionSource functionQ
    eb ec en functionBase profileBase t a c u0 v0 theta0 profile marker marker_name cb cc cn
    x u y z lowBase lowInput qInput du inA eq0 childInput bodyInput
    thetaXY dx imageRest imageBody image qOut dy :
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
  quotation_safe M eb ec en x t -> coding_lt M cb x ->
  coding_lt M a x -> coding_lt M c x -> coding_lt M y x -> coding_lt M x u -> coding_lt M u z ->
  coding_lt M u0 u -> coding_lt M v0 u ->
  quotient_pair_safe M t x a lowBase -> quotation_atom M false x a t lowBase lowInput ->
  coding_lt M lowInput u -> quotation_atom M false x a t u qInput ->
  raw_dmem_witness_graph M t x a u qInput du inA eq0 childInput bodyInput ->
  coding_lt M bodyInput z ->
  binary_matrix_quotation M phi eb ec en x y (succM M z) t thetaXY ->
  membership_graph M t x dx -> quotation_binary M SFAnd lowInput thetaXY imageRest ->
  quotation_binary M SFAnd dx imageRest imageBody -> named_exists_graph M x imageBody image ->
  membership_graph M t y dy -> stable_context_support M cb cc cn dy ->
  quotation_atom M false y c t z qOut -> contextually_provable M cb cc cn image ->
  contextually_provable M cb cc cn qOut.
Proof.
  intros HB RA RB GF FQ HFBase PF HM PM NU0 NV0 HUV HPBase Q0 GP PP HX HCb
    HAX HCX HYX HXU HUZ HU0U HV0U HLowSafe GIL HLow GInput RawI HBody
    QXY DX RestI BodyI ExI DY PY GOut PImage.
  set (k:=succM M z).
  assert (HXZ:coding_lt M x z) by exact (coding_lt_trans M x u z HXU HUZ).
  assert (HYZ:coding_lt M y z) by exact (coding_lt_trans M y x z HYX HXZ).
  assert (HCZ:coding_lt M c z) by exact (coding_lt_trans M c x z HCX HXZ).
  assert (HTZ:coding_lt M t z) by exact (coding_lt_trans M t x z (proj1 HX) HXZ).
  assert (HAZ:coding_lt M a z) by exact (coding_lt_trans M a x z HAX HXZ).
  assert (HZ:coding_lt M z k) by apply coding_lt_succ.
  assert (HX0:x<>zeroM M).
  { intro E;rewrite E in HAX;exact (coding_not_lt_zero M a HAX). }
  assert (HU0:u<>zeroM M).
  { intro E;rewrite E in HXU;exact (coding_not_lt_zero M x HXU). }
  assert (HZ0:z<>zeroM M).
  { intro E;rewrite E in HUZ;exact (coding_not_lt_zero M u HUZ). }
  assert (HSZ:quotation_safe M eb ec en z t).
  { split;[exact HTZ|]. intros i value HV;exact (coding_lt_trans M value x z ((proj2 HX) i value HV) HXZ). }
  assert (HSK:quotation_safe M eb ec en k t).
  { split;[exact (coding_lt_trans M t z k HTZ HZ)|].
    intros i value HV;exact (coding_lt_trans M value z k ((proj2 HSZ) i value HV) HZ). }
  assert (EU:environment_avoids_name M eb ec en u).
  { intros i value HV E;subst value;exact (template_lt_different M u u
      (coding_lt_trans M u x u ((proj2 HX) i u HV) HXU) eq_refl). }
  assert (EZ:environment_avoids_name M eb ec en z).
  { intros i value HV E;subst value;exact (template_lt_different M z z ((proj2 HSZ) i z HV) eq_refl). }
  assert (NU:raw_clause_usable_name M eb ec en t a c k u).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t u (coding_lt_trans M t x u (proj1 HX) HXU) (eq_sym E)).
    - exact (fun E=>template_lt_different M a u (coding_lt_trans M a x u HAX HXU) (eq_sym E)).
    - exact (fun E=>template_lt_different M c u (coding_lt_trans M c x u HCX HXU) (eq_sym E)).
    - exact (coding_lt_trans M u z k HUZ HZ). }
  assert (NZ:raw_clause_usable_name M eb ec en t a c k z).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t z HTZ (eq_sym E)).
    - exact (fun E=>template_lt_different M a z HAZ (eq_sym E)).
    - exact (fun E=>template_lt_different M c z HCZ (eq_sym E)). }
  assert (NU0K:raw_clause_usable_name M eb ec en t a c k u0).
  { destruct NU0 as [H0 [HT [HA [HC [HL HE]]]]];repeat split;try assumption.
    exact (coding_lt_trans M u0 u k HU0U (coding_lt_trans M u z k HUZ HZ)). }
  assert (NV0K:raw_clause_usable_name M eb ec en t a c k v0).
  { destruct NV0 as [H0 [HT [HA [HC [HL HE]]]]];repeat split;try assumption.
    exact (coding_lt_trans M v0 u k HV0U (coding_lt_trans M u z k HUZ HZ)). }
  destruct (binary_matrix_total M phi eb ec en u z k t) as [thetaUZ QUZ].
  destruct (binary_matrix_total M phi eb ec en u y k t) as [thetaUY QUY].
  destruct (code_relation_total M (E_wal (CEvar 3) E_raw_coverage_clause)
    (raw_clause_parameters M t a c u z thetaUZ)) as [allcoverage GAC].
  destruct (code_relation_total M (E_wal (CEvar 4) E_raw_support_clause)
    (raw_clause_parameters M t a c u z thetaUZ)) as [allsupport GAS].

  assert (PC:stable_context_support M cb cc cn allcoverage).
  { exact (proj1 (stable_raw_profile_rebased_clauses M cb cc cn phi eb ec en t a c profileBase k
      u0 v0 u z theta0 thetaUZ profile allcoverage allsupport HPBase HSK
      (proj1 (proj2 (proj2 (proj2 (proj2 NU0))))) (proj1 (proj2 (proj2 (proj2 (proj2 NV0)))))
      NU0K NV0K NU NZ
      (fun E=>template_lt_different M u0 u HU0U (eq_sym E)) HUV
      (fun E=>template_lt_different M u0 z (coding_lt_trans M u0 u z HU0U HUZ) (eq_sym E))
      (fun E=>template_lt_different M v0 u HV0U (eq_sym E))
      (fun E=>template_lt_different M v0 z (coding_lt_trans M v0 u z HV0U HUZ) (eq_sym E))
      (fun E=>template_lt_different M u z HUZ (eq_sym E)) Q0 QUZ GP GAC GAS PP)). }
  destruct (code_relation_total M E_raw_coverage_clause (raw_clause_parameters M t a c u z thetaUZ))
    as [coverage GCoverage].
  destruct (raw_coverage_clause_parts M t a c u z thetaUZ coverage GCoverage)
    as (du' & inA' & guard & dz' & memz' & rest & source & exsource & hasbody & has & inner &
        DU' & IN' & GUARD & DZ' & MZ' & REST & SOURCE & EXSOURCE & HASBODY & HAS & INNER & COVERAGE).
  pose proof RawI as [DU [INA [EQ0 [CHILDINPUT [BODYINPUT EXINPUT]]]]].
  assert (du'=du) by exact (tagged_pair_functional M 1 t u du' du DU' DU).
  assert (inA'=inA) by exact (tagged_pair_functional M 1 u a inA' inA IN' INA).
  subst du' inA'.
  assert (guard=childInput) by exact (quotation_binary_functional M SFAnd du inA guard childInput GUARD CHILDINPUT).
  subst guard.
  destruct (raw_dmem_witness_graph_total M t y c z qOut GOut)
    as (dz & memz & eqYZ & childOut & outBody & RawOut).
  pose proof RawOut as [DZ [MZ [EQYZ [CHILDOUT [BODYOUT EXOUT]]]]].
  assert (dz'=dz) by exact (tagged_pair_functional M 1 t z dz' dz DZ' DZ).
  assert (memz'=memz) by exact (tagged_pair_functional M 1 z c memz' memz MZ' MZ).
  subst dz' memz'.
  set (rho:=collection_coverage_parameters M dz memz thetaUZ thetaUY eqYZ).
  assert (GRest:code_relation M rho (E_wa (CEvar 1) (CEvar 2)) rest).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 1) (CEvar 2)
      memz thetaUZ rest eq_refl eq_refl) REST). }
  assert (GSource:code_relation M rho (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) source).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 0) (E_wa (CEvar 1) (CEvar 2))
      dz rest source eq_refl GRest) SOURCE). }
  assert (GHas:quotation_quantifier M false z t thetaUZ has).
  { exact (proj2 (quotation_guarded_exists_graph M z t thetaUZ dz hasbody has DZ HASBODY) HAS). }
  assert (GAll:universal_graph M u coverage allcoverage).
  { exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u z thetaUZ)
      (CEvar 3) E_raw_coverage_clause u coverage allcoverage eq_refl GCoverage) GAC). }
  assert (HAbsent:named_binder_absent M coverage u).
  { apply (raw_coverage_clause_binder_absent M t a c u z thetaUZ coverage u);[exact (template_lt_different M u z HUZ)| |exact GCoverage].
    exact (binary_matrix_binder_absent M phi eb ec en u z k t thetaUZ u QUZ (coding_lt_trans M u z k HUZ HZ)). }
  assert (FreshOutX:formula_fresh M qOut x).
  { exact (quotation_atom_fresh M false y c t z qOut x GOut HXZ HX0
      (fun E=>template_lt_different M y x HYX (eq_sym E))
      (fun E=>template_lt_different M c x HCX (eq_sym E))
      (fun E=>template_lt_different M t x (proj1 HX) (eq_sym E))). }
  assert (FreshOutU:formula_fresh M qOut u).
  { exact (quotation_atom_fresh M false y c t z qOut u GOut HUZ HU0
      (fun E=>template_lt_different M y u (coding_lt_trans M y x u HYX HXU) (eq_sym E))
      (fun E=>template_lt_different M c u (coding_lt_trans M c x u HCX HXU) (eq_sym E))
      (fun E=>template_lt_different M t u (coding_lt_trans M t x u (proj1 HX) HXU) (eq_sym E))). }
  assert (FreshBodyU:formula_fresh M imageBody u).
  { apply (raw_image_body_fresh M t x dx lowInput thetaXY imageRest imageBody u DX RestI BodyI HU0).
    - exact (fun E=>template_lt_different M t u (coding_lt_trans M t x u (proj1 HX) HXU) (eq_sym E)).
    - exact (fun E=>template_lt_different M x u HXU (eq_sym E)).
    - exact (formula_above_is_fresh M lowInput u HLow).
    - exact (binary_matrix_formula_fresh M phi eb ec en x y k t thetaXY u QXY
        (coding_lt_trans M u z k HUZ HZ) HU0
        (template_lt_different M t u (coding_lt_trans M t x u (proj1 HX) HXU))
        (fun E=>template_lt_different M x u HXU (eq_sym E))
        (fun E=>template_lt_different M y u (coding_lt_trans M y x u HYX HXU) (eq_sym E)) EU). }
  assert (FreshBodyZ:formula_fresh M imageBody z).
  { apply (raw_image_body_fresh M t x dx lowInput thetaXY imageRest imageBody z DX RestI BodyI HZ0).
    - exact (fun E=>template_lt_different M t z HTZ (eq_sym E)).
    - exact (fun E=>template_lt_different M x z HXZ (eq_sym E)).
    - exact (formula_above_is_fresh M lowInput z (coding_lt_trans M lowInput u z HLow HUZ)).
    - exact (binary_matrix_formula_fresh M phi eb ec en x y k t thetaXY z QXY HZ HZ0
        (template_lt_different M t z HTZ)
        (fun E=>template_lt_different M x z HXZ (eq_sym E))
        (fun E=>template_lt_different M y z HYZ (eq_sym E)) EZ). }
  destruct (environment_cons_total M cb cc cn imageBody) as [bb [bc [bn CImage]]].
  assert (Include:context_included M cb cc cn bb bc bn).
  { intros f HF;apply (proj2 (context_member_cons M cb cc cn imageBody bb bc bn f CImage));now right. }
  apply (contextual_witness_bind M cb cc cn x imageBody image qOut bb bc bn
    (context_fresh_above_code M cb cc cn x HCb) FreshOutX ExI CImage PImage).
  assert (PBody:stable_context_support M bb bc bn imageBody).
  { apply stable_context_support_member;apply (proj2 (context_member_cons M cb cc cn imageBody bb bc bn imageBody CImage));now left. }
  assert (PRest:stable_context_support M bb bc bn imageRest).
  { exact (stable_context_support_conjunction_right M bb bc bn dx imageRest imageBody BodyI PBody). }
  assert (PTheta:stable_context_support M bb bc bn thetaXY).
  { exact (stable_context_support_conjunction_right M bb bc bn lowInput thetaXY imageRest RestI PRest). }
  assert (PLow:contextually_provable M bb bc bn lowInput).
  { apply stable_context_support_here;exact (stable_context_support_conjunction_left M bb bc bn lowInput thetaXY imageRest RestI PRest). }
  assert (PInput:contextually_provable M bb bc bn qInput).
  { apply (contextual_equivalent_forward M bb bc bn lowInput qInput);[|exact PLow].
    destruct HLowSafe as [HB0 [HT0 [HX0' HA0]]].
    exact (quotation_atom_rebase M false x a t lowBase u lowInput qInput HB0
      ltac:(exact (coding_lt_trans M (zeroM M) x u (environment_below_zero M eb ec en x (proj2 HX)) HXU))
      HX0' HA0 HT0 HXU (coding_lt_trans M a x u HAX HXU) (coding_lt_trans M t x u (proj1 HX) HXU) GIL GInput). }
  destruct (environment_cons_total M bb bc bn bodyInput) as [ob [oc [on CInput]]].
  destruct (environment_cons_total M ob oc on source) as [ib [ic [ine CSource]]].
  assert (FreshU:context_fresh M bb bc bn u).
  { apply (proj2 (context_fresh_cons M cb cc cn imageBody bb bc bn u CImage));split.
    - exact FreshBodyU.
    - exact (context_fresh_above_code M cb cc cn u (coding_lt_trans M cb x u HCb HXU)). }
  assert (FreshZ:context_fresh M ob oc on z).
  { apply (proj2 (context_fresh_cons M bb bc bn bodyInput ob oc on z CInput));split.
    - exact (formula_above_is_fresh M bodyInput z HBody).
    - apply (proj2 (context_fresh_cons M cb cc cn imageBody bb bc bn z CImage));split.
      + exact FreshBodyZ.
      + exact (context_fresh_above_code M cb cc cn z (coding_lt_trans M cb x z HCb HXZ)). }
  apply (quotient_coverage_from_quotient_input M phi count ra rb functionSource functionQ eb ec en functionBase
    t a c marker marker_name bb bc bn x u y z dy thetaXY thetaUY thetaUZ qInput du inA eq0 childInput bodyInput
    dz memz eqYZ childOut outBody qOut source exsource has inner coverage allcoverage ob oc on ib ic ine);
    try assumption.
  - exact (stable_context_support_included M cb cc cn bb bc bn marker Include PM).
  - repeat split.
    + exact (coding_lt_trans M (zeroM M) x u (environment_below_zero M eb ec en x (proj2 HX)) HXU).
    + exact (coding_lt_trans M t x u (proj1 HX) HXU).
    + exact HXU.
    + exact (coding_lt_trans M a x u HAX HXU).
  - exact (stable_context_support_included M cb cc cn bb bc bn allcoverage Include PC).
  - exact (stable_context_support_included M cb cc cn bb bc bn functionQ Include PF).
  - exact (stable_context_support_included M cb cc cn bb bc bn dy Include PY).
Qed.

Print Assumptions raw_image_body_fresh.
Print Assumptions profile_coverage_at_fresh_witnesses.


