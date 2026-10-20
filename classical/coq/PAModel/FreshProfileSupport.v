(** The forward image implication from one actual raw Collection profile.
    Both witness names and every intermediate syntax graph are constructed.
    No numerical existential is unpacked as a semantic witness. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeDescent CodeTags FreshNames CodeExpressions NumericalProofs
  NumericalEquivalence NumericalVacuitySteps NamedLeibnizSteps NamedExistential NamedBinderFresh
  NumericalEnvironments NumericalContexts ContextualProofs StableContextSupport
  SourceBounded QuotationHygiene QuotationPayloads QuotationAtomRebase QuotationFixedSource SetFormulaCodes
  SupportedQuotientEnvironments RawQuotientAtomCongruence RawCollectionProfile RawClauseAlpha RawClauseHygiene
  RawDmemWitness RawClauseGraphs QuotientSupportFromRawCollection ActualCollectionSupport
  CollectionWitnessKernels BinaryMatrixRenaming MatrixClauseRenaming ProfileRebasedClauses
  HybridImageGraphs HybridImageFresh ContextFreshBounds ReplacementFreshAllocation
  ReplacementMatrixQuotation TemplateNamedSubstitution QuotedSameBaseRules SubstitutionEnvironmentTotal.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem fresh_profile_support_image M phi count eb ec en oldbase t a c u0 v0 theta0 profile
    marker marker_name cb cc cn y z q :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  raw_clause_usable_name M eb ec en t a c oldbase u0 ->
  raw_clause_usable_name M eb ec en t a c oldbase v0 -> u0<>v0 ->
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en z t ->
  coding_lt M cb z -> coding_lt M a z -> coding_lt M u0 z -> coding_lt M v0 z ->
  quotient_pair_safe M t y c z ->
  binary_matrix_quotation M phi eb ec en u0 v0 oldbase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M cb cc cn profile ->
  quotation_atom M false y c t z q -> contextually_provable M cb cc cn q ->
  exists u k image, coding_lt M z u /\ coding_lt M u k /\
    hybrid_image_graph M phi eb ec en t a y u k k image /\
    formula_fresh M image z /\ contextually_provable M cb cc cn image.
Proof.
  intros HB HM PM NU0 NV0 HU0V0 HOld HZ HCbZ HAZ HU0Z HV0Z HSafe Q0 GP PP GQ PQ.
  destruct (raw_dmem_witness_graph_total M t y c z q GQ)
    as [dz [memz [eq0 [childz [bodyz Raw]]]]].
  destruct (environment_cons_total M cb cc cn bodyz) as [ob [oc [on CO]]].
  set (u:=replacement_name_bound M (cons ob (cons z nil))).
  assert (HObU:coding_lt M ob u) by (apply replacement_name_bound_above;now left).
  assert (HZU:coding_lt M z u) by (apply replacement_name_bound_above;now right;left).
  set (k:=succM M u).
  assert (HUK:coding_lt M u k) by apply coding_lt_succ.
  assert (HZK:coding_lt M z k) by exact (coding_lt_trans M z u k HZU HUK).
  destruct HSafe as [HZ0 [HTZ [HYZ HCZ]]].
  assert (HK0:coding_lt M (zeroM M) k) by exact (coding_lt_trans M (zeroM M) z k HZ0 HZK).
  assert (HK:quotation_safe M eb ec en k t).
  { split;[exact (coding_lt_trans M t z k HTZ HZK)|].
    intros i v HV;exact (coding_lt_trans M v z k ((proj2 HZ) i v HV) HZK). }

  assert (HZneq:z<>zeroM M) by exact (template_lt_different M (zeroM M) z HZ0).
  assert (HUneq:u<>zeroM M).
  { exact (template_lt_different M (zeroM M) u (coding_lt_trans M (zeroM M) z u HZ0 HZU)). }
  assert (EU:environment_avoids_name M eb ec en u).
  { intros i v HV E;subst v.
    exact (template_lt_different M u u (coding_lt_trans M u z u ((proj2 HZ) i u HV) HZU) eq_refl). }
  assert (EZ:environment_avoids_name M eb ec en z).
  { intros i v HV E;subst v;exact (template_lt_different M z z ((proj2 HZ) i z HV) eq_refl). }
  assert (NU:raw_clause_usable_name M eb ec en t a c k u).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t u (coding_lt_trans M t z u HTZ HZU) (eq_sym E)).
    - exact (fun E=>template_lt_different M a u (coding_lt_trans M a z u HAZ HZU) (eq_sym E)).
    - exact (fun E=>template_lt_different M c u (coding_lt_trans M c z u HCZ HZU) (eq_sym E)). }
  assert (NZ:raw_clause_usable_name M eb ec en t a c k z).
  { repeat split;try assumption.
    - exact (fun E=>template_lt_different M t z HTZ (eq_sym E)).
    - exact (fun E=>template_lt_different M a z HAZ (eq_sym E)).
    - exact (fun E=>template_lt_different M c z HCZ (eq_sym E)). }
  assert (NU0K:raw_clause_usable_name M eb ec en t a c k u0).
  { destruct NU0 as [H0 [HT [HA [HC [HL HE]]]]];repeat split;try assumption.
    exact (coding_lt_trans M u0 z k HU0Z HZK). }
  assert (NV0K:raw_clause_usable_name M eb ec en t a c k v0).
  { destruct NV0 as [H0 [HT [HA [HC [HL HE]]]]];repeat split;try assumption.
    exact (coding_lt_trans M v0 z k HV0Z HZK). }
  assert (HU0U:u0<>u) by exact (fun E=>template_lt_different M u0 u (coding_lt_trans M u0 z u HU0Z HZU) (eq_sym E)).
  assert (HU0Z':u0<>z) by exact (fun E=>template_lt_different M u0 z HU0Z (eq_sym E)).
  assert (HV0U:v0<>u) by exact (fun E=>template_lt_different M v0 u (coding_lt_trans M v0 z u HV0Z HZU) (eq_sym E)).
  assert (HV0Z':v0<>z) by exact (fun E=>template_lt_different M v0 z HV0Z (eq_sym E)).
  assert (HUZ:u<>z) by exact (template_lt_different M z u HZU).
  destruct (binary_matrix_total M phi eb ec en u z k t) as [thetaZ QT].
  destruct (hybrid_image_graph_total M phi eb ec en t a y u k k) as [image Image].
  assert (FI:formula_fresh M image z).
  { apply (hybrid_image_formula_fresh M phi eb ec en t a y u k k image z Image HZneq HUZ).
    - exact (fun E=>template_lt_different M t z HTZ (eq_sym E)).
    - exact (fun E=>template_lt_different M a z HAZ (eq_sym E)).
    - exact (fun E=>template_lt_different M y z HYZ (eq_sym E)).
        - exact HZK.
    - exact HZK.
    - exact EZ. }
  destruct (code_relation_total M (E_wal (CEvar 3) E_raw_coverage_clause)
    (raw_clause_parameters M t a c u z thetaZ)) as [allcoverage GAC].
  destruct (code_relation_total M (E_wal (CEvar 4) E_raw_support_clause)
    (raw_clause_parameters M t a c u z thetaZ)) as [allsupport GAS].
  pose proof (stable_raw_profile_rebased_clauses M cb cc cn phi eb ec en t a c oldbase k
    u0 v0 u z theta0 thetaZ profile allcoverage allsupport
    HOld HK (proj1 (proj2 (proj2 (proj2 (proj2 NU0)))))
    (proj1 (proj2 (proj2 (proj2 (proj2 NV0))))) NU0K NV0K NU NZ
    HU0U HU0V0 HU0Z' HV0U HV0Z' HUZ Q0 QT GP GAC GAS PP) as [_ PS].
  destruct (code_relation_total M E_raw_support_clause (raw_clause_parameters M t a c u z thetaZ))
    as [support GS].
  destruct (raw_support_clause_parts M t a c u z thetaZ support GS)
    as (du & ma & childU & source & exsource & dz' & memz' & guard & DU & MA & CU & SRC & EXS & DZ' & MZ' & GUARD & SUPPORT).
  pose proof Raw as [DZ [MZ [EQ0 [CZ [BZ EXQ]]]]].
  assert (Edz:dz'=dz) by exact (tagged_pair_functional M 1 t z dz' dz DZ' DZ).
  assert (Emem:memz'=memz) by exact (tagged_pair_functional M 1 z c memz' memz MZ' MZ).
  subst dz' memz'.
  assert (Eguard:guard=childz) by exact (quotation_binary_functional M SFAnd dz memz guard childz GUARD CZ).
  subst guard.
  pose proof Image as [qu [thetaY [di [restI [bodyI [QU [TY [DI [RI [BI EXI]]]]]]]]]].
  assert (Edi:di=du) by exact (tagged_pair_functional M 1 t u di du DI DU).
  subst di.
  destruct (quotation_atom_total M true y z t k) as [eq EQ].
  set (rho:=collection_support_parameters M du ma qu thetaZ thetaY eq).
  assert (GChild:code_relation M rho (E_wa (CEvar 0) (CEvar 1)) childU).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 0) (CEvar 1)
      du ma childU eq_refl eq_refl) CU). }
  assert (GSource:code_relation M rho (support_input (CEvar 0) (CEvar 1) (CEvar 3)) source).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (E_wa (CEvar 0) (CEvar 1)) (CEvar 3)
      childU thetaZ source GChild eq_refl) SRC). }
  assert (GRest:code_relation M rho (E_wa (CEvar 2) (CEvar 4)) restI).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 2) (CEvar 4)
      qu thetaY restI eq_refl eq_refl) RI). }
  assert (GTarget:code_relation M rho (support_output (CEvar 0) (CEvar 2) (CEvar 4)) bodyI).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 0) (E_wa (CEvar 2) (CEvar 4))
      du restI bodyI eq_refl GRest) BI). }
  destruct (environment_cons_total M ob oc on source) as [ib [ic [ine CI]]].
  exists u,k,image;split;[exact HZU|]. split;[exact HUK|]. split;[exact Image|]. split;[exact FI|].
  apply (quotient_support_from_raw_collection M phi count eb ec en cb cc cn marker marker_name
    t a c u y z k du ma qu thetaZ thetaY eq q dz memz eq0 childz bodyz source bodyI exsource image
    support allsupport ob oc on ib ic ine);try assumption.
  - exact (coding_lt_trans M a z k HAZ HZK).
  - exact (coding_lt_trans M y z k HYZ HZK).
  - repeat split;assumption.
  - exact (proj1 (expression_universal_iff M (raw_clause_parameters M t a c u z thetaZ)
      (CEvar 4) E_raw_support_clause z support allsupport eq_refl GS) GAS).
  - apply (raw_support_clause_binder_absent M t a c u z thetaZ support z HUZ);[|exact GS].
    exact (binary_matrix_binder_absent M phi eb ec en u z k t thetaZ z QT HZK).
  - exact (context_fresh_above_code M cb cc cn z HCbZ).
  - exact (context_fresh_above_code M ob oc on u HObU).
Qed.

Print Assumptions fresh_profile_support_image.







Theorem profile_support_target_image M phi count eb ec en oldbase t a c u0 v0 theta0 profile
    marker marker_name cb cc cn y z q x atomBase matrixBase target :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  raw_clause_usable_name M eb ec en t a c oldbase u0 ->
  raw_clause_usable_name M eb ec en t a c oldbase v0 -> u0<>v0 ->
  quotation_safe M eb ec en oldbase t -> quotation_safe M eb ec en z t ->
  coding_lt M cb z -> coding_lt M a z -> coding_lt M u0 z -> coding_lt M v0 z ->
  quotient_pair_safe M t y c z ->
  binary_matrix_quotation M phi eb ec en u0 v0 oldbase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M cb cc cn profile ->
  quotation_atom M false y c t z q -> contextually_provable M cb cc cn q ->
  quotation_safe M eb ec en x t -> coding_lt M a x -> coding_lt M y x -> coding_lt M x z ->
  quotient_pair_safe M t x a atomBase -> quotation_safe M eb ec en matrixBase t ->
  coding_lt M x matrixBase -> coding_lt M y matrixBase ->
  hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase target ->
  contextually_provable M cb cc cn target.
Proof.
  intros HB HM PM NU0 NV0 HUV HOld HZ HCb HAZ HU0Z HV0Z HS Q0 GP PP GQ PQ
    HX HAX HYX HXZ HAtom HMatrix HXM HYM Target.
  destruct (fresh_profile_support_image M phi count eb ec en oldbase t a c u0 v0 theta0 profile
    marker marker_name cb cc cn y z q HB HM PM NU0 NV0 HUV HOld HZ HCb HAZ HU0Z HV0Z HS Q0 GP PP GQ PQ)
    as [u [k [image [HZU [HUK [Image [FI PI]]]]]]].
  destruct (hybrid_image_graph_total M phi eb ec en t a y x k k) as [imageX ImageX].
  destruct HS as [HZ0 [HTZ [HYZ HCZ]]].
  assert (HXU:coding_lt M x u) by exact (coding_lt_trans M x z u HXZ HZU).
  assert (HXK:coding_lt M x k) by exact (coding_lt_trans M x u k HXU HUK).
  assert (HYK:coding_lt M y k) by exact (coding_lt_trans M y z k HYZ (coding_lt_trans M z u k HZU HUK)).
  assert (HAK:coding_lt M a k) by exact (coding_lt_trans M a z k HAZ (coding_lt_trans M z u k HZU HUK)).
  assert (HTK:coding_lt M t k) by exact (coding_lt_trans M t z k HTZ (coding_lt_trans M z u k HZU HUK)).
  assert (HK0:coding_lt M (zeroM M) k) by exact (coding_lt_trans M (zeroM M) z k HZ0 (coding_lt_trans M z u k HZU HUK)).
  assert (HU0:u<>zeroM M) by exact (template_lt_different M (zeroM M) u (coding_lt_trans M (zeroM M) z u HZ0 HZU)).
  assert (HX0:x<>zeroM M) by exact (template_lt_different M (zeroM M) x (environment_below_zero M eb ec en x (proj2 HX))).
  assert (EX:environment_avoids_name M eb ec en x).
  { intros i value HV E;subst value;exact (template_lt_different M x x ((proj2 HX) i x HV) eq_refl). }
  assert (EU:environment_avoids_name M eb ec en u).
  { intros i value HV E;subst value;exact (template_lt_different M u u
      (coding_lt_trans M u z u ((proj2 HZ) i u HV) HZU) eq_refl). }
  assert (EQ:numerical_equivalent M image imageX).
  { apply (hybrid_image_alpha M phi eb ec en t a y u x k k image imageX);try assumption.
    - exact (template_lt_different M x u HXU).
    - exact (fun E=>template_lt_different M t u (coding_lt_trans M t z u HTZ HZU) (eq_sym E)).
    - exact (fun E=>template_lt_different M a u (coding_lt_trans M a z u HAZ HZU) (eq_sym E)).
    - exact (fun E=>template_lt_different M y u (coding_lt_trans M y z u HYZ HZU) (eq_sym E)).
    - exact (fun E=>template_lt_different M t x (proj1 HX) (eq_sym E)).
    - exact (fun E=>template_lt_different M a x HAX (eq_sym E)).
    - exact (fun E=>template_lt_different M y x HYX (eq_sym E)). }
  apply (contextual_equivalent_forward M cb cc cn imageX target);[|exact (contextual_equivalent_forward M cb cc cn image imageX EQ PI)].
  apply (hybrid_image_rebase M phi eb ec en t a y x k k atomBase matrixBase imageX target);try assumption.
  - repeat split;assumption.
  - split;[exact HTK|]. intros i value HV;exact (coding_lt_trans M value z k ((proj2 HZ) i value HV)
      (coding_lt_trans M z u k HZU HUK)).
Qed.

Print Assumptions profile_support_target_image.




Theorem raw_profile_implies_quotient_image M phi count eb ec en oldbase t a c u0 v0 theta0 profile
    marker marker_name cb cc cn y qbase q x atomBase matrixBase target :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  raw_clause_usable_name M eb ec en t a c oldbase u0 ->
  raw_clause_usable_name M eb ec en t a c oldbase v0 -> u0<>v0 ->
  quotation_safe M eb ec en oldbase t ->
  binary_matrix_quotation M phi eb ec en u0 v0 oldbase t theta0 ->
  code_relation M (raw_clause_parameters M t a c u0 v0 theta0)
    (E_raw_collection_profile (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) profile ->
  stable_context_support M cb cc cn profile ->
  quotient_pair_safe M t y c qbase -> quotation_atom M false y c t qbase q ->
  contextually_provable M cb cc cn q ->
  quotation_safe M eb ec en x t -> coding_lt M a x -> coding_lt M y x ->
  quotient_pair_safe M t x a atomBase -> quotation_safe M eb ec en matrixBase t ->
  coding_lt M x matrixBase -> coding_lt M y matrixBase ->
  hybrid_image_graph M phi eb ec en t a y x atomBase matrixBase target ->
  contextually_provable M cb cc cn target.
Proof.
  intros HB HM PM NU0 NV0 HUV HOld Q0 GP PP HQSafe HQ PQ HX HAX HYX HA HMtx HXM HYM Target.
  set (names:=cons cb (cons eb (cons t (cons a (cons c (cons u0 (cons v0 (cons x (cons y (cons (zeroM M) nil)))))))))).
  set (z:=replacement_name_bound M names).
  assert (Large:forall r,In r names -> coding_lt M r z).
  { intros r HR;exact (replacement_name_bound_above M names r HR). }
  assert (HCb:coding_lt M cb z) by (apply Large;unfold names;simpl;tauto).
  assert (HEb:coding_lt M eb z) by (apply Large;unfold names;simpl;tauto).
  assert (HT:coding_lt M t z) by (apply Large;unfold names;simpl;tauto).
  assert (HZ0:coding_lt M (zeroM M) z) by (apply Large;unfold names;simpl;tauto).
  assert (HY:coding_lt M y z) by (apply Large;unfold names;simpl;tauto).
  assert (HC:coding_lt M c z) by (apply Large;unfold names;simpl;tauto).
  assert (HZ:quotation_safe M eb ec en z t).
  { split;[exact HT|exact (environment_below_above_code M eb ec en z HEb HZ0)]. }
  destruct (quotation_atom_total M false y c t z) as [qz GQz].
  assert (PQz:contextually_provable M cb cc cn qz).
  { apply (contextual_equivalent_forward M cb cc cn q qz);[|exact PQ].
    destruct HQSafe as [HB0 [HT0 [HY0 HC0]]].
    exact (quotation_atom_rebase M false y c t qbase z q qz HB0 HZ0 HY0 HC0 HT0 HY HC HT HQ GQz). }
  apply (profile_support_target_image M phi count eb ec en oldbase t a c u0 v0 theta0 profile
    marker marker_name cb cc cn y z qz x atomBase matrixBase target);try assumption.
  - apply Large;unfold names;simpl;tauto.
  - apply Large;unfold names;simpl;tauto.
  - apply Large;unfold names;simpl;tauto.
  - repeat split;assumption.
  - apply Large;unfold names;simpl;tauto.
Qed.

Print Assumptions raw_profile_implies_quotient_image.

