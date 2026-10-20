(** Specialize the actual ordinal-range upper bound at a witnessed member.
    The result is the literal raw subset formula, proved by ordinary AllE. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution
  SubstitutionSource SourceInstantiationConstructors SourceBounded NumericalSourceFull
  SourceDerivedRules SourceFilterMemberIntroduction SourceOrdinalUnion SourceOrdinalPredicate
  SourceWFSeparationConstructor SourceFunctionalityShells SchemaConstructorBounds SourcePropositionalRebase
  NumericalRenamingMaps NumericalRenaming SourceQuantifierRules SourceFilteredProfileShift.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Definition source_oc_subset_graph M x y subset := exists left right point,
  sf_relation M SFMember (zeroM M) (succM M x) left /\
  sf_relation M SFMember (zeroM M) (succM M y) right /\
  sf_relation M SFImpl left right point /\sf_relation M SFAll point (zeroM M) subset.
Definition source_oc_upper_point_graph M s u all := exists member subset point,
  sf_relation M SFMember (zeroM M) (succM M s) member /\
  source_oc_subset_graph M (zeroM M) (succM M u) subset /\
  sf_relation M SFImpl member subset point /\sf_relation M SFAll point (zeroM M) all.

Theorem source_oc_subset_total M x y :exists subset,source_oc_subset_graph M x y subset.
Proof.
  destruct (sf_relation_total M SFMember (zeroM M) (succM M x)) as (left&HL).
  destruct (sf_relation_total M SFMember (zeroM M) (succM M y)) as (right&HR).
  destruct (sf_relation_total M SFImpl left right) as (point&HP).
  destruct (sf_relation_total M SFAll point (zeroM M)) as (subset&HA).
  exists subset,left,right,point. auto.
Qed.

Theorem source_oc_subset_renaming M x y subset x' y' out rb rc rn delta :
  source_oc_subset_graph M x y subset ->renaming_lookup M rb rc rn delta x x' ->
  renaming_lookup M rb rc rn delta y y' ->numerical_renaming M subset rb rc rn delta out ->
  source_oc_subset_graph M x' y' out.
Proof.
  intros (left&right&point&HL&HR&HP&HA) HX HY HS.
  destruct (proj1 (numerical_renaming_quantifier M true point subset rb rc rn delta out HA) HS)
    as (ab&ac&an&point'&HMap&RPoint&HAll).
  destruct (proj1 (numerical_renaming_binary M SFImpl left right point ab ac an delta point'
    (or_intror (or_intror eq_refl)) HP) RPoint) as (left'&right'&RL&RR&HPoint).
  assert (HAtom:forall z z' a a',renaming_lookup M rb rc rn delta z z' ->
      sf_relation M SFMember (zeroM M) (succM M z) a ->
      numerical_renaming M a ab ac an delta a' ->
      sf_relation M SFMember (zeroM M) (succM M z') a').
  { intros z z' a a' HZ HShape RA.
    destruct (proj1 (numerical_renaming_member M _ _ a ab ac an delta a' HShape) RA)
      as (u&v&HU&HV&HOut).
    pose proof (renaming_lookup_functional M ab ac an delta _ u _ HU (proj1 (proj2 HMap))) as EU.
    subst u.
    pose proof (renaming_lookup_functional M ab ac an delta _ v _ HV
      (proj2 (proj2 HMap) z z' HZ)) as EV. now subst v. }
  exists left',right',point'. split;[exact (HAtom x x' left left' HX HL RL)|].
  split;[exact (HAtom y y' right right' HY HR RR)|auto].
Qed.

Theorem source_oc_upper_point_shift M s u all shifted :
  source_oc_upper_point_graph M s u all ->source_formula_shift M all shifted ->
  source_oc_upper_point_graph M (succM M s) (succM M u) shifted.
Proof.
  intros (member&subset&point&HM&HS&HP&HA) HR.
  destruct (proj1 (numerical_renaming_quantifier M true point all (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) shifted HA) HR) as (rb&rc&rn&point'&HMap&RPoint&HAll).
  destruct (proj1 (numerical_renaming_binary M SFImpl member subset point rb rc rn
    (code_numeral M 1) point' (or_intror (or_intror eq_refl)) HP) RPoint)
    as (member'&subset'&RM&RS&HPoint).
  destruct (proj1 (numerical_renaming_member M _ _ member rb rc rn (code_numeral M 1)
    member' HM) RM) as (x&y&HX&HY&HMember).
  pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1) _ x _ HX
    (proj1 (proj2 HMap))) as EX. subst x.
  pose proof (renaming_lookup_functional M rb rc rn (code_numeral M 1) _ y _ HY
    (proj2 (proj2 HMap) s (succM M s) (source_shift_map_lookup M s))) as EY. subst y.
  exists member',subset',point'. split;[exact HMember|].
  split;[|auto]. exact (source_oc_subset_renaming M (zeroM M) (succM M u) subset
    (zeroM M) (succM M (succM M u)) subset' rb rc rn (code_numeral M 1) HS
    (proj1 (proj2 HMap))
    (proj2 (proj2 HMap) u (succM M u) (source_shift_map_lookup M u)) RS).
Qed.

Theorem source_oc_subset_head_instantiation M u d raw subset :
  source_oc_subset_graph M (zeroM M) (succM M u) raw ->
  source_oc_subset_graph M d u subset ->numerical_instantiation M raw d subset.
Proof.
  intros (left&right&point&HL&HR&HP&HA) (left'&right'&point'&HL'&HR'&HP'&HA').
  destruct (substitution_singleton_total M d) as (b&c&HH&HT).
  destruct (substitution_lift_total M b c (code_numeral M 1) (zeroM M)) as (rb&rc&rn&HMap).
  assert (HLeft:numerical_substitution M left rb rc rn (code_numeral M 1) left').
  { apply (proj2 (numerical_substitution_member M (zeroM M) (code_numeral M 1) left
      rb rc rn (code_numeral M 1) left' HL)).
    exists (zeroM M),(succM M d). split;[exact (proj1 (proj2 HMap))|].
    split;[exact (proj2 (proj2 HMap) (zeroM M) d HH)|exact HL']. }
  assert (HRight:numerical_substitution M right rb rc rn (code_numeral M 1) right').
  { apply (proj2 (numerical_substitution_member M (zeroM M) (succM M (succM M u)) right
      rb rc rn (code_numeral M 1) right' HR)).
    exists (zeroM M),(succM M u). split;[exact (proj1 (proj2 HMap))|].
    split;[exact (proj2 (proj2 HMap) (succM M u) u (substitution_singleton_tail M b c u))|exact HR']. }
  assert (HPoint:numerical_substitution M point rb rc rn (code_numeral M 1) point').
  { apply (proj2 (numerical_substitution_binary M SFImpl left right point rb rc rn
      (code_numeral M 1) point' (or_intror (or_intror eq_refl)) HP)). exists left',right'. auto. }
  exists b,c. split;[exact HH|].
  apply (proj2 (numerical_substitution_quantifier M true point raw b c (code_numeral M 1)
    (zeroM M) subset HA)). exists rb,rc,rn,point'. auto.
Qed.

Theorem source_full_oc_upper_member M b c n s u d all member subset :
  source_oc_upper_point_graph M s u all ->sf_relation M SFMember d s member ->
  source_oc_subset_graph M d u subset ->source_full_prv M b c n all ->
  source_full_prv M b c n member ->source_full_prv M b c n subset.
Proof.
  intros (rawmember&rawsubset&point&HM&HS&HP&HA) HMember HSubset PAll PMember.
  destruct (sf_relation_total M SFImpl member subset) as (instance&HI).
  pose proof (source_instantiation_binary M SFImpl rawmember rawsubset point d member subset instance
    (or_intror (or_intror eq_refl)) HP
    (source_member_zero_successor_instantiation M s d rawmember member HM HMember)
    (source_oc_subset_head_instantiation M u d rawsubset subset HS HSubset) HI) as HInst.
  apply (source_full_modus_ponens M b c n member subset instance HI);[|exact PMember].
  exact (full_source_AllE M b c n point all d instance
    (source_wf_quantifier_instance M b c n SFAll point all d instance (or_introl eq_refl)
      HA (source_full_prv_wellformed M b c n all PAll) HInst) PAll HA HInst).
Qed.

Theorem source_ordinal_upper_shell M upper :source_ordinal_upper_graph M upper ->
  exists all body,source_oc_upper_point_graph M (code_numeral M 1) (zeroM M) all /\
    sf_relation M SFAnd (source_ordinal_predicate_code M) all body /\
    sf_relation M SFEx body (zeroM M) upper.
Proof.
  intro HG. unfold source_ordinal_upper_graph,E_ordinal_range_upper in HG.
  destruct (schema_expression_quantifier_split M _ SFEx _ upper HG) as (body&HB&HE).
  destruct (schema_expression_split M _ SFAnd _ _ body HB) as (ordinal&all&HO&HA&HBody).
  change (ordinal=source_ordinal_predicate_code M) in HO. subst ordinal.
  destruct (schema_expression_quantifier_split M _ SFAll _ all HA) as (point&HP&HAll).
  destruct (schema_expression_split M _ SFImpl _ _ point HP) as (member&subset&HM&HS&HPoint).
  destruct (schema_expression_quantifier_split M _ SFAll _ subset HS) as (subpoint&HSP&HSubset).
  destruct (schema_expression_split M _ SFImpl _ _ subpoint HSP) as (left&right&HL&HR&HSubpoint).
  assert (HMem:sf_relation M SFMember (zeroM M) (code_numeral M 2) member).
  { exact (proj1 (schema_expression_graph M (fun _=>source_ordinal_predicate_code M) SFMember
      (CEconst 0) (CEconst 2) (zeroM M) (code_numeral M 2) member eq_refl eq_refl) HM). }
  assert (HLeft:sf_relation M SFMember (zeroM M) (code_numeral M 1) left).
  { exact (proj1 (schema_expression_graph M (fun _=>source_ordinal_predicate_code M) SFMember
      (CEconst 0) (CEconst 1) (zeroM M) (code_numeral M 1) left eq_refl eq_refl) HL). }
  assert (HRight:sf_relation M SFMember (zeroM M) (code_numeral M 2) right).
  { exact (proj1 (schema_expression_graph M (fun _=>source_ordinal_predicate_code M) SFMember
      (CEconst 0) (CEconst 2) (zeroM M) (code_numeral M 2) right eq_refl eq_refl) HR). }
  exists all,body. split;[|auto]. exists member,subset,point. split;[exact HMem|].
  split;[exists left,right,subpoint;auto|auto].
Qed.

Print Assumptions source_oc_subset_head_instantiation.
Print Assumptions source_full_oc_upper_member.
Print Assumptions source_ordinal_upper_shell.
Print Assumptions source_oc_subset_renaming.
Print Assumptions source_oc_upper_point_shift.
