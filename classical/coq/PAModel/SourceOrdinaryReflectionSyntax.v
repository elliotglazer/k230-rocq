(** Literal ordinary reflection syntax from pinned Z_refl.Refl. This graph
    computes a formula; it makes no mathematical reflection assertion. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs NumericalSubstitutionMaps SetFormulaCodes SourceBounded SourceBoundMonotone
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationBounds
  SourceSetRelativization SourceSetRelativizationFunctionality SourceSetRelativizationBounds
  SourceHierarchySyntax SourceCommonLevelRecipe SourceIffGraphs SourceBallS SourceBallSBounds SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_ordinary_reflection M domain count phi d out:=exists left right equiv block level point,
  source_relativization M domain phi left /\source_set_relativization M count phi right /\
  source_iff_graph M left right equiv /\source_ballS M count(zeroM M)equiv block /\
  source_LL_instance M(succM M d)(zeroM M)level /\sf_relation M SFImpl level block point /\
  sf_relation M SFAll point(zeroM M)out.
Definition source_ordinary_reflection_formula(domain count phi d out:term):form:=∃∃∃∃∃∃(
  source_relativization_formula(source_common_lift6 domain)(source_common_lift6 phi)$5 ∧
  source_set_relativization_formula(source_common_lift6 count)(source_common_lift6 phi)$4 ∧
  source_iff_formula $5 $4 $3 ∧source_ballS_formula(source_common_lift6 count)zero $3 $2 ∧
  source_LL_literal_formula(σ(source_common_lift6 d))zero $1 ∧sf_formula SFImpl $1 $2 $0 ∧
  sf_formula SFAll $0 zero(source_common_lift6 out)).
Local Opaque holds source_relativization_formula source_set_relativization_formula source_iff_formula
  source_ballS_formula source_LL_literal_formula sf_formula.
Theorem source_ordinary_reflection_formula_correct M rho domain count phi d out:
  holds M rho(source_ordinary_reflection_formula domain count phi d out)<->
  source_ordinary_reflection M(evalM M rho domain)(evalM M rho count)(evalM M rho phi)(evalM M rho d)(evalM M rho out).
Proof.
  unfold source_ordinary_reflection_formula,source_ordinary_reflection.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_relativization_formula_correct. setoid_rewrite source_set_relativization_formula_correct.
  setoid_rewrite source_iff_formula_correct. setoid_rewrite source_ballS_formula_correct.
  setoid_rewrite source_LL_literal_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite substitution_map_eval_succ. unfold evalM,source_common_lift6. repeat setoid_rewrite eval_up.
  split;intros(a&b&e&bl&l&p&H);exists a,b,e,bl,l,p;tauto.
Qed.
Theorem source_ordinary_reflection_total M domain count phi d:exists out,source_ordinary_reflection M domain count phi d out.
Proof.
  destruct(source_relativization_total M domain phi)as(left&HL).
  destruct(source_set_relativization_total M count phi)as(right&HR).
  destruct(source_iff_total M left right)as(equiv&HE).
  destruct(source_ballS_total M count(zeroM M)equiv)as(block&HB).
  destruct(source_LL_instance_total M(succM M d)(zeroM M))as(level&HLevel).
  destruct(sf_relation_total M SFImpl level block)as(point&HPoint).
  destruct(sf_relation_total M SFAll point(zeroM M))as(out&HOut).
  exists out,left,right,equiv,block,level,point. repeat split;assumption.
Qed.
Theorem source_ordinary_reflection_functional M domain count phi d out out':
  source_ordinary_reflection M domain count phi d out->source_ordinary_reflection M domain count phi d out'->out=out'.
Proof.
  intros(a&b&e&bl&l&p&HA&HB&HE&HBL&HL&HP&HO)(a'&b'&e'&bl'&l'&p'&HA'&HB'&HE'&HBL'&HL'&HP'&HO').
  pose proof(source_relativization_functional M phi domain a a' HA HA')as E. subst a'.
  pose proof(source_set_relativization_functional M phi count b b' HB HB')as E. subst b'.
  pose proof(source_iff_functional M a b e e' HE HE')as E. subst e'.
  pose proof(source_ballS_functional M count(zeroM M)e bl bl' HBL HBL')as E. subst bl'.
  pose proof(source_LL_instance_functional M(succM M d)(zeroM M)l l' HL HL')as E. subst l'.
  pose proof(sf_relation_functional M SFImpl l bl p p' HP HP')as E. subst p'.
  exact(sf_relation_functional M SFAll p(zeroM M)out out' HO HO').
Qed.
Theorem source_ordinary_reflection_bounded M domain count phi d out k:
  source_bounded M domain(code_numeral M 1)->source_bounded M phi count->coding_lt M d k->
  source_ordinary_reflection M domain count phi d out->source_bounded M out k.
Proof.
  intros HD HPh HDK(a&b&e&bl&l&p&HA&HB&HE&HBL&HL&HP&HO).
  pose proof(source_relativization_preserves_bound M phi domain count a HD HPh HA)as BA.
  assert(BPhi1:source_bounded M phi(succM M count)).
  { exact(source_bounded_monotone M phi count(succM M count)HPh
      (proj2(coding_lt_succ_cases M count(succM M count))(or_introl(coding_lt_succ M count)))). }
  pose proof(source_set_relativization_preserves_bound M phi count(succM M count)b(coding_lt_succ M count)BPhi1 HB)as BB.
  assert(BA1:source_bounded M a(succM M count)).
  { exact(source_bounded_monotone M a count(succM M count)BA
      (proj2(coding_lt_succ_cases M count(succM M count))(or_introl(coding_lt_succ M count)))). }
  pose proof(source_iff_bounded M a b e(succM M count)BA1 BB HE)as BE.
  assert(BE':source_bounded M e(addM M count(code_numeral M 1))).
  { change(source_bounded M e(addM M count(succM M(zeroM M)))). now rewrite internal_add_succ_right,coding_add_zero_r. }
  pose proof(source_ballS_bounded M count(zeroM M)e bl(code_numeral M 1)HBL(coding_zero_lt_succ M(zeroM M))BE')as BBL.
  pose proof(source_LL_instance_bounded M(succM M d)(zeroM M)l(succM M k)
    (proj2(coding_lt_succ_cancel M d k)HDK)(coding_zero_lt_succ M k)HL)as BL.
  pose proof(sr_domain_bound_succ M bl k BBL)as BBL'.
  apply(proj2(source_bounded_accept_unary M SFAll p out k(or_introl eq_refl)HO)).
  apply(proj2(source_bounded_accept_binary M SFImpl l bl p(succM M k)(or_intror(or_intror eq_refl))HP)). auto.
Qed.
Print Assumptions source_ordinary_reflection_formula_correct.
Print Assumptions source_ordinary_reflection_total.
Print Assumptions source_ordinary_reflection_functional.
Print Assumptions source_ordinary_reflection_bounded.


