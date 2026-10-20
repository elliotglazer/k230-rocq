(** An actual proof step for two exterior ordinal names around Dn. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
  NumericalRenaming NumericalSubstitution SourceFiniteCutoffShift SourceQfFunctionality SourceQuantifierRules NumericalContextRenaming
  SourceDnStep SourceDnRotation4 SourceDnCutoffDiamonds SourceDnCarrierSyntax SourceDnCarrierTools
  SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorConditionalMap
  SourceCarrierUniversalMap SourceMemberReverseEquality SourcePropositionalRebase SourceFunctionalityShells SourceZFRProvability SourceSetTheoryDescriptors.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_zfr_dn_carrier_step M condition prev dn pa pb outA outB priorMap prior result final k :
  sf_relation M SFEqual(code_numeral M 1)(code_numeral M 2)condition ->
  source_bounded M prev(succM M(succM M(succM M k))) ->
  source_dn_successor M prev dn ->
  source_cutoff_shift M 2 prev pa ->source_cutoff_shift M 1 prev pb ->
  source_cutoff_shift M 2 dn outA ->source_cutoff_shift M 1 dn outB ->
  sf_relation M SFImpl pa pb priorMap ->sf_relation M SFImpl condition priorMap prior ->
  sf_relation M SFImpl outA outB result ->sf_relation M SFImpl condition result final ->
  source_zfr_provable M prior ->source_zfr_provable M final.
Proof.
  intros HCondition HB HD HPA HPB HOA HOB HPM HPr HRes HFinal PPr.
  assert(HC:source_bounded M condition(code_numeral M 3)).
  { apply(proj2(source_bounded_accept_atom M SFEqual(code_numeral M 1)(code_numeral M 2)condition(code_numeral M 3)
      (or_intror eq_refl)HCondition)). split;[apply coding_lt_succ_cancel,coding_zero_lt_succ|apply coding_lt_succ]. }
  destruct(numerical_renaming_total M pa(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)) as(a&HRA).
  destruct(numerical_renaming_total M pb(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)) as(b&HRB).
  destruct(numerical_renaming_total M condition(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(shifted&HCShift).
  pose proof(source_dn_carrier_rotate4_condition M condition shifted HC HCShift) as HRC.
  destruct(source_dn_carrier_successor_cutoff_inv M 2 prev dn outA ltac:(lia) HD
    HOA) as(ra&ta&ga&qa&HRotA&HTA&HGA&HQA&HAllA).
  destruct(source_dn_carrier_successor_cutoff_inv M 1 prev dn outB ltac:(lia) HD HOB) as(rb&tb&gb&qb&HRotB&HTB&HGB&HQB&HAllB).
  pose proof(source_dn_carrier_rotate_cutoff_square M 2 prev pa ra a (succM M(succM M(succM M k)))
    ltac:(lia) HB HPA HRotA HRA) as HA.
  pose proof(source_dn_carrier_rotate_cutoff_square M 1 prev pb rb b (succM M(succM M(succM M k)))
    ltac:(lia) HB HPB HRotB HRB) as HB'.
  assert(EA:ta=a) by(eapply source_cutoff_shift_functional;[exact HTA|exact HA]). subst ta.
  assert(EB:tb=b) by(eapply source_cutoff_shift_functional;[exact HTB|exact HB']). subst tb.
  destruct(sf_relation_total M SFImpl a b) as(ab&HAB).
  destruct(sf_relation_total M SFImpl shifted ab) as(point&HPoint).
  assert(HRen:numerical_renaming M prior(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M) point).
  { apply(proj2(numerical_renaming_binary M SFImpl condition priorMap prior _ _ _ _ point
      (or_intror(or_intror eq_refl)) HPr)). exists shifted,ab. split;[exact HRC|]. split;[|exact HPoint].
    apply(proj2(numerical_renaming_binary M SFImpl pa pb priorMap _ _ _ _ ab
      (or_intror(or_intror eq_refl)) HPM)). exists a,b. auto. }
  pose proof(source_descriptor_provable_renaming M ZFRSourceDescriptor prior _ _ _ _ point
    (proj2(source_zfr_descriptor_provable M prior)PPr) HRen) as PPoint.
  assert(HPA0:source_bounded M pa(succM M(succM M(succM M(succM M k))))).
  { exact(source_cutoff_shift_bounded M 2 prev pa (succM M k) HB
      HPA). }
  assert(HPB0:source_bounded M pb(succM M(succM M(succM M(succM M k))))).
  { exact(source_cutoff_shift_bounded M 1 prev pb (succM M(succM M k)) HB HPB). }
  pose proof(source_dn_rotate4_bounded M pa a k HPA0 HRA) as HBA.
  pose proof(source_dn_rotate4_bounded M pb b k HPB0 HRB) as HBB.
  assert(HC0:source_bounded M condition(succM M(succM M(succM M k)))).
  { apply(source_bounded_monotone M condition(code_numeral M 3) _ HC).
    apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HBG:source_bounded M ga(succM M(succM M(succM M(succM M k))))).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ ga _ (or_introl eq_refl) HGA)). split.
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HBGb:source_bounded M gb(succM M(succM M(succM M(succM M k))))).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ gb _ (or_introl eq_refl)HGB)). split.
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HShiftEq:sf_relation M SFEqual(code_numeral M 2)(code_numeral M 3)shifted).
  { destruct(proj1(numerical_renaming_equal M(code_numeral M 1)(code_numeral M 2)condition
      (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)shifted HCondition)HCShift)
      as(x&y&HX&HY&HEq).
    pose proof(proj1(context_shift_lookup M(code_numeral M 1)x)HX)as EX.
    pose proof(proj1(context_shift_lookup M(code_numeral M 2)y)HY)as EY. subst x y. exact HEq. }
  destruct(sf_relation_total M SFImpl gb ga)as(gm&HGM).
  destruct(sf_relation_total M SFImpl shifted gm)as(guardlaw&HGuardLaw).
  set(rho:=fun i:nat=>match i with 0=>zeroM M|1=>code_numeral M 2|_=>code_numeral M 3 end).
  assert(HGuardGraph:code_relation M rho source_member_reverse_equality_expression guardlaw).
  { change(code_relation M rho(E_sf SFImpl(E_sf SFEqual(CEvar 1)(CEvar 2))
      (E_sf SFImpl(E_sf SFMember(CEvar 0)(CEvar 2))(E_sf SFMember(CEvar 0)(CEvar 1))))guardlaw).
    unfold rho. functionality_graph. }
  pose proof(source_zfr_member_reverse_equality M rho guardlaw HGuardGraph)as PGuard.
  destruct(sf_relation_total M SFImpl qa qb)as(pointmap&HPointMap).
  destruct(sf_relation_total M SFImpl shifted pointmap)as(combined&HCombined).
  exact(source_zfr_conditional_two_guard_universal M condition shifted a b ga gb ab point gm guardlaw
    qa qb pointmap combined outA outB result final(succM M(succM M(succM M k)))
    HC0 HCShift HBA HBB HBG HBGb HAB HPoint HGM HGuardLaw HQA HQB HPointMap HCombined HAllA HAllB
    HRes HFinal(proj1(source_zfr_descriptor_provable M point)PPoint)PGuard).
Qed.

Print Assumptions source_zfr_dn_carrier_step.
