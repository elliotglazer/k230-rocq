(** An actual proof step for two exterior ordinal names around Dn. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
  NumericalRenaming NumericalSubstitution SourceFiniteCutoffShift SourceQfFunctionality SourceQuantifierRules
  SourceDnStep SourceDnRotation4 SourceDnCutoffDiamonds SourceDnConditionalTools
  SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorConditionalMap.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_descriptor_dn_conditional_step M T condition prev dn pa pb outA outB priorMap prior result final k :
  source_bounded M condition(code_numeral M 2) ->
  source_bounded M prev(succM M(succM M(succM M k))) ->
  source_dn_successor M prev dn ->
  source_formula_shift M prev pa ->source_cutoff_shift M 1 prev pb ->
  source_formula_shift M dn outA ->source_cutoff_shift M 1 dn outB ->
  sf_relation M SFImpl pa pb priorMap ->sf_relation M SFImpl condition priorMap prior ->
  sf_relation M SFImpl outA outB result ->sf_relation M SFImpl condition result final ->
  source_descriptor_provable M T prior ->source_descriptor_provable M T final.
Proof.
  intros HC HB HD HPA HPB HOA HOB HPM HPr HRes HFinal PPr.
  destruct(numerical_renaming_total M pa(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)) as(a&HRA).
  destruct(numerical_renaming_total M pb(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M)) as(b&HRB).
  destruct(numerical_renaming_total M condition(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)) as(shifted&HCShift).
  pose proof(source_dn_rotate4_condition M condition shifted HC HCShift) as HRC.
  destruct(source_dn_successor_cutoff_inv M 0 prev dn outA ltac:(lia) HD
    (proj1(source_formula_shift_cutoff_zero M dn outA) HOA)) as(ra&ta&ga&qa&HRotA&HTA&HGA&HQA&HAllA).
  destruct(source_dn_successor_cutoff_inv M 1 prev dn outB ltac:(lia) HD HOB) as(rb&tb&gb&qb&HRotB&HTB&HGB&HQB&HAllB).
  pose proof(source_dn_rotate_cutoff_square M 0 prev pa ra a (succM M(succM M(succM M k)))
    ltac:(lia) HB(proj1(source_formula_shift_cutoff_zero M prev pa) HPA) HRotA HRA) as HA.
  pose proof(source_dn_rotate_cutoff_square M 1 prev pb rb b (succM M(succM M(succM M k)))
    ltac:(lia) HB HPB HRotB HRB) as HB'.
  assert(EA:ta=a) by(eapply source_cutoff_shift_functional;[exact HTA|exact HA]). subst ta.
  assert(EB:tb=b) by(eapply source_cutoff_shift_functional;[exact HTB|exact HB']). subst tb.
  assert(EG:gb=ga) by(eapply sf_relation_functional;[exact HGB|exact HGA]). subst gb.
  destruct(sf_relation_total M SFImpl a b) as(ab&HAB).
  destruct(sf_relation_total M SFImpl shifted ab) as(point&HPoint).
  assert(HRen:numerical_renaming M prior(code_numeral M 5475)(code_numeral M 6)(code_numeral M 4)(zeroM M) point).
  { apply(proj2(numerical_renaming_binary M SFImpl condition priorMap prior _ _ _ _ point
      (or_intror(or_intror eq_refl)) HPr)). exists shifted,ab. split;[exact HRC|]. split;[|exact HPoint].
    apply(proj2(numerical_renaming_binary M SFImpl pa pb priorMap _ _ _ _ ab
      (or_intror(or_intror eq_refl)) HPM)). exists a,b. auto. }
  pose proof(source_descriptor_provable_renaming M T prior _ _ _ _ point PPr HRen) as PPoint.
  assert(HPA0:source_bounded M pa(succM M(succM M(succM M(succM M k))))).
  { exact(source_cutoff_shift_bounded M 0 prev pa (succM M(succM M(succM M k))) HB
      (proj1(source_formula_shift_cutoff_zero M prev pa) HPA)). }
  assert(HPB0:source_bounded M pb(succM M(succM M(succM M(succM M k))))).
  { exact(source_cutoff_shift_bounded M 1 prev pb (succM M(succM M k)) HB HPB). }
  pose proof(source_dn_rotate4_bounded M pa a k HPA0 HRA) as HBA.
  pose proof(source_dn_rotate4_bounded M pb b k HPB0 HRB) as HBB.
  assert(HC0:source_bounded M condition(succM M(succM M(succM M k)))).
  { apply(source_bounded_monotone M condition(code_numeral M 2) _ HC).
    apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  assert(HBG:source_bounded M ga(succM M(succM M(succM M(succM M k))))).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ ga _ (or_introl eq_refl) HGA)). split.
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_lt_succ_cancel,coding_lt_succ_cancel,coding_zero_lt_succ. }
  exact(source_descriptor_conditional_universal_map M T condition shifted a b ga ab point qa qb outA outB result final
    (succM M(succM M(succM M k))) HC0 HCShift HBA HBB HBG HAB HPoint HQA HQB HAllA HAllB HRes HFinal PPoint).
Qed.

Print Assumptions source_descriptor_dn_conditional_step.
