(** A PA-definable support condition for two arbitrary internal source
    substitutions. It records actual conditional equality certificates. *)
From PAModel Require Import Model NumericalProofs FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalContextRenaming NumericalRenamingMaps NumericalRenaming SourceQuantifierRules
 SourceConditionalProofs SourceEqualityAtomFacts SourceZFRProvability SourceDescriptorProvability
 SourceDescriptorClosure SourceSetTheoryDescriptors SourceImplicationAllShift SourceShiftSpecialization.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_equal_substitutions M condition k rb rc rn base sb sc sn sbase:=
 forall i x y equal,coding_lt M i k ->substitution_lookup M rb rc rn base i x ->
 substitution_lookup M sb sc sn sbase i y ->sf_relation M SFEqual x y equal ->
 source_conditional_fact M condition equal.
Definition source_support_lift4(t:term):=t`[↑]`[↑]`[↑]`[↑].
Definition source_equal_substitutions_formula(condition k rb rc rn base sb sc sn sbase:term):form:=
 ∀∀∀∀(Peano.sless $3(source_support_lift4 k) →
 substitution_lookup_formula(source_support_lift4 rb)(source_support_lift4 rc)(source_support_lift4 rn)(source_support_lift4 base)$3 $2 →
 substitution_lookup_formula(source_support_lift4 sb)(source_support_lift4 sc)(source_support_lift4 sn)(source_support_lift4 sbase)$3 $1 →
 sf_formula SFEqual $2 $1 $0 →source_conditional_fact_formula(source_support_lift4 condition)$0).
Local Opaque holds sf_formula substitution_lookup_formula source_conditional_fact_formula.
Theorem source_equal_substitutions_formula_correct M rho condition k rb rc rn base sb sc sn sbase:
 holds M rho(source_equal_substitutions_formula condition k rb rc rn base sb sc sn sbase) <->
 source_equal_substitutions M(evalM M rho condition)(evalM M rho k)
 (evalM M rho rb)(evalM M rho rc)(evalM M rho rn)(evalM M rho base)
 (evalM M rho sb)(evalM M rho sc)(evalM M rho sn)(evalM M rho sbase).
Proof.
 unfold source_equal_substitutions_formula,source_equal_substitutions.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite less_formula_correct. setoid_rewrite substitution_lookup_formula_correct.
 setoid_rewrite sf_formula_correct. setoid_rewrite source_conditional_fact_formula_correct.
 unfold source_support_lift4,evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Local Transparent evalM.

Theorem source_equal_substitutions_lift M condition shifted k rb rc rn base sb sc sn sbase
 rd re rm sd se sm q:
 source_bounded M condition q ->source_formula_shift M condition shifted ->
 source_equal_substitutions M condition k rb rc rn base sb sc sn sbase ->
 substitution_lift M rb rc rn base rd re rm ->substitution_lift M sb sc sn sbase sd se sm ->
 source_equal_substitutions M shifted(succM M k)rd re rm(succM M base)sd se sm(succM M sbase).
Proof.
 intros BC HS HSupport HR HT i x y equal HI HX HY HE law HLaw.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)i)as[EZ|[j EJ]].
 - subst i.
   assert(EX:x=zeroM M)by(eapply substitution_lookup_functional;[exact HX|exact(proj1(proj2 HR))]).
   assert(EY:y=zeroM M)by(eapply substitution_lookup_functional;[exact HY|exact(proj1(proj2 HT))]).
   subst x y.
   apply(source_conditional_fact_of_proof M shifted equal(succM M q));[| |exact(source_zfr_equal_reflexive M _ equal HE)|exact HLaw].
   + exact(source_shift_bound M condition shifted q BC HS).
   + exact(proj2(source_bounded_accept_atom M SFEqual _ _ equal(succM M q)(or_intror eq_refl)HE)
     (conj(coding_zero_lt_succ M q)(coding_zero_lt_succ M q))).
 - subst i.
   pose proof(proj1(coding_lt_succ_cancel M j k)HI)as HJ.
   destruct(substitution_lookup_total M rb rc rn base j)as(u&HU).
   destruct(substitution_lookup_total M sb sc sn sbase j)as(v&HV).
   assert(EX:x=succM M u)by(eapply substitution_lookup_functional;[exact HX|exact(proj2(proj2 HR)j u HU)]).
   assert(EY:y=succM M v)by(eapply substitution_lookup_functional;[exact HY|exact(proj2(proj2 HT)j v HV)]).
   subst x y.
   destruct(sf_relation_total M SFEqual u v)as(oldEqual&HOldEqual).
   destruct(sf_relation_total M SFImpl condition oldEqual)as(oldLaw&HOldLaw).
   pose proof(HSupport j u v oldEqual HJ HU HV HOldEqual oldLaw HOldLaw)as POld.
   assert(HShiftEqual:numerical_renaming M oldEqual(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)equal).
   { apply(proj2(numerical_renaming_equal M u v oldEqual(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)equal HOldEqual)).
     exists(succM M u),(succM M v). repeat split;try assumption;apply context_shift_lookup;reflexivity. }
   assert(HShiftLaw:numerical_renaming M oldLaw(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)law).
   { apply(proj2(numerical_renaming_binary M SFImpl condition oldEqual oldLaw(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)law
      (or_intror(or_intror eq_refl))HOldLaw)).
     exists shifted,equal. repeat split;assumption. }
   apply(proj1(source_zfr_descriptor_provable M law)).
   exact(source_descriptor_provable_renaming M ZFRSourceDescriptor oldLaw(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)law
    (proj2(source_zfr_descriptor_provable M oldLaw)POld)HShiftLaw).
Qed.
Print Assumptions source_equal_substitutions_formula_correct.
Print Assumptions source_equal_substitutions_lift.
