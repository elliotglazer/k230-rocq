(** Actual existential elimination in the two arithmetic cases of NumF < succession. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceQuantifierRules SourceFiniteCutoffShift NumericalRenaming
 NumericalInstantiation SourceDefinabilityStep SourceDefinabilityPrimitives SourceDefinabilityLogicalStep
 SourceNumFUniqueSyntax SourceNumFUniqueStep SourceNumFClosureBounds SourceNumFClosurePrograms
 SourceNumFLessRecipe SourceNumFLessFacts SourceNumFLessPrograms SourceImplicationAllShift
 SourcePropositionalTemplates SourceWitnessProofComposition SourceNumeralLift SourceZFRProvability.
From Undecidability.FOL Require Import Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Local Opaque source_def_successor01 numf_successor02.
Theorem source_zfr_numf_less_step_core M equal r p q rs ri relationLaw result :
 source_bounded M r(code_numeral M 1) ->source_bounded M p(code_numeral M 1) ->source_def_step M false p q ->
 source_formula_shift M r rs ->sf_relation M SFImpl p(numf_comparison_atom M equal)ri ->
 sf_relation M SFImpl rs ri relationLaw ->source_zfr_provable M relationLaw ->
 source_numf_less_recipe M r q(zeroM M)(code_numeral M 1)result ->source_zfr_provable M result.
Proof.
 intros BR BP HStep HRS HRI HRLaw PRel(a&b&e&i&HA&HB&HE&HI&HOut).
 assert(E:a=r)by(eapply numerical_instantiation_functional;[exact HA|exact(source_unit_instantiation_self M r BR)]). subst a.
 destruct(source_numf_step_comparison_structure M p q BP HStep)as(ps&pair&shifted&pair2&pair3&q1&q2&
  HPS&HPair&HQ&HPairShifted&HPairShift&HPair2&HQ1&HQShift&HPair3&HQ2&HQ1Shift).
 pose proof(source_def_numeral_step_bound M p q BP HStep)as BQ.
 assert(E:b=q1)by(eapply numerical_instantiation_functional;[exact HB|exact(source_unit_instantiation_shift M q q1 BQ HQShift)]). subst b.
 assert(E:e=code_numeral M(sf_make SFMember 0 1))by(eapply sf_relation_functional;[exact HE|exact(sf_make_numeral M SFMember 0 1)]). subst e.
 pose proof(source_shift_bound M r rs(code_numeral M 1)BR HRS)as BRS.
 pose proof(source_shift_bound M q q1(code_numeral M 1)BQ HQShift)as BQ1.
 pose proof(source_numf_bound_to_six M r 1 ltac:(lia)BR)as BR6.
 pose proof(source_numf_bound_to_six M p 1 ltac:(lia)BP)as BP6.
 pose proof(source_numf_bound_to_six M rs 2 ltac:(lia)BRS)as BRS6.
 pose proof(source_numf_bound_to_six M q1 2 ltac:(lia)BQ1)as BQ16.
 pose proof(source_cutoff_shift_bounded M 1 _ _(code_numeral M 1)(numerical_def_successor_bound M)(proj1(source_numf_successor_cutoffs M)))as BS02.
 pose proof(source_numf_bound_to_six M _ 3 ltac:(lia)BS02)as BS026.
 assert(BR10:source_bounded M(numf_comparison_atom M equal)(code_numeral M 6)).
 { apply(proj2(source_bounded_accept_atom M(if equal then SFEqual else SFMember)(code_numeral M 1)(zeroM M)_(code_numeral M 6)
    ltac:(destruct equal;[right|left];reflexivity)(sf_make_numeral M(if equal then SFEqual else SFMember)1 0))).
   split;[apply coding_lt_succ_cancel,coding_zero_lt_succ|apply coding_zero_lt_succ]. }
 assert(BM01:source_bounded M(code_numeral M(sf_make SFMember 0 1))(code_numeral M 6)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 1)_(code_numeral M 6)(or_introl eq_refl)(sf_make_numeral M SFMember 0 1))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel,coding_zero_lt_succ]. }
 assert(BM12:source_bounded M(code_numeral M(sf_make SFMember 1 2))(code_numeral M 6)).
 { apply(proj2(source_bounded_accept_atom M SFMember(code_numeral M 1)(code_numeral M 2)_(code_numeral M 6)(or_introl eq_refl)(sf_make_numeral M SFMember 1 2))).
   split;[apply coding_lt_succ_cancel,coding_zero_lt_succ|do 2 apply coding_lt_succ_cancel;apply coding_zero_lt_succ]. }
 destruct(source_numf_less_fact_shell M equal)as(factInner&fact&HFI&HF&PFact).
 destruct(sf_relation_total M SFImpl r(code_numeral M(sf_make SFMember 0 1)))as(target&HTarget).
 destruct(sf_relation_total M SFImpl rs(code_numeral M(sf_make SFMember 1 2)))as(targetShift&HTargetShift).
 assert(HMShift:source_formula_shift M(code_numeral M(sf_make SFMember 0 1))(code_numeral M(sf_make SFMember 1 2))).
 { exact(source_formula_numeral_shift M($0 ∈' $1)). }
 pose proof(source_implication_shift_graph M r _ target rs _ targetShift HTarget HTargetShift HRS HMShift)as HTShift.
 destruct(sf_relation_total M SFImpl pair2 targetShift)as(point&HPoint).
 set(env:=fun idx:nat=>match idx with 0=>rs|1=>p|2=>numf_comparison_atom M equal|
  3=>code_numeral M(sf_encode numf_successor02)|_=>code_numeral M(sf_make SFMember 1 2)end).
 assert(PPoint:source_zfr_provable M point).
 { apply(source_zfr_prop_two M nl_old nl_fact nl_point source_numf_less_point_program env(code_numeral M 6)relationLaw fact point).
   - intros[|[|[|[|idx]]]];cbn[env];assumption.
   - unfold nl_old. nu_graph.
   - unfold nl_fact. nu_graph.
   - unfold nl_point. nu_graph.
   - exact PRel.
   - exact PFact. }
 assert(BTarget:source_bounded M target(code_numeral M 6)).
 { exact(proj2(source_bounded_accept_binary M SFImpl r _ target(code_numeral M 6)(or_intror(or_intror eq_refl))HTarget)(conj BR6 BM01)). }
 destruct(sf_relation_total M SFImpl q1 target)as(map&HMap).
 pose proof(source_zfr_exists_implication M pair2 q1 target targetShift point map(code_numeral M 6)(code_numeral M 6)
  BQ16 BTarget HQ1 HTShift HPoint HMap PPoint)as PMap.
 set(lastenv:=fun idx:nat=>match idx with 0=>q1|1=>r|_=>code_numeral M(sf_make SFMember 0 1)end).
 apply(source_zfr_prop_one M _ _ source_numf_closure_reverse_point_program lastenv(code_numeral M 6)map result).
 - intros[|[|idx]];cbn[lastenv];assumption.
 - nu_graph.
 - nu_graph.
 - exact PMap.
Qed.
Print Assumptions source_zfr_numf_less_step_core.
