(** Distinct internal indices have source-provably distinct numeral values. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded
 SourceDefinabilityBounds SourceDefinabilityLogicalStep SourceNumFLessRecipe SourceNumFLessInduction
 SourceNumFDistinctRecipe SourceNumFDistinctFixed SourceNumFDistinctComposition SourceNumFClosureBounds
 SourceImplicationAllShift SourceQuantifierRules NumericalRenaming NumericalInstantiation SourceZFRProvability.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_zfr_numf_distinct_ordered M (reverse:bool) k l p q out:
 (if reverse then coding_lt M l k else coding_lt M k l) ->source_numf M k p ->source_numf M l q ->
 source_numf_distinct_recipe M p q(zeroM M)(code_numeral M 1)out ->source_zfr_provable M out.
Proof.
 intros HK HP HQ(a&b&e&neg&inner&HA&HB&HE&HN&HI&HO).
 pose proof(source_numf_bound M k p HP)as BP. pose proof(source_numf_bound M l q HQ)as BQ.
 assert(E:a=p)by(eapply numerical_instantiation_functional;[exact HA|exact(source_unit_instantiation_self M p BP)]). subst a.
 destruct(numerical_renaming_total M q(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(qs&HQS).
 assert(E:b=qs)by(eapply numerical_instantiation_functional;[exact HB|exact(source_unit_instantiation_shift M q qs BQ HQS)]). subst b.
 assert(E:e=code_numeral M(sf_make SFEqual 0 1))by(eapply sf_relation_functional;[exact HE|exact(sf_make_numeral M SFEqual 0 1)]). subst e.
 destruct(source_numf_distinct_fact_shell M reverse)as(neg'&fact&HN'&HF&PF).
 assert(E:neg'=neg)by(eapply sf_relation_functional;eassumption). subst neg'.
 destruct(sf_relation_total M SFImpl(if reverse then p else qs)(numf_distinct_member M reverse))as(mi&HMI).
 destruct(sf_relation_total M SFImpl(if reverse then qs else p)mi)as(ml&HML).
 assert(PM:source_zfr_provable M ml).
 { destruct reverse.
   - apply(source_zfr_numf_less_uniform M k l q p(code_numeral M 1)(zeroM M)ml HK HQ HP).
     exists qs,p,(numf_distinct_member M true),mi. repeat split.
     + exact(source_unit_instantiation_shift M q qs BQ HQS).
     + exact(source_unit_instantiation_self M p BP).
     + exact(sf_make_numeral M SFMember 1 0).
     + exact HMI.
     + exact HML.
   - apply(source_zfr_numf_less_uniform M l k p q(zeroM M)(code_numeral M 1)ml HK HP HQ).
     exists p,qs,(numf_distinct_member M false),mi. repeat split.
     + exact(source_unit_instantiation_self M p BP).
     + exact(source_unit_instantiation_shift M q qs BQ HQS).
     + exact(sf_make_numeral M SFMember 0 1).
     + exact HMI.
     + exact HML. }
 pose proof(source_numf_bound_to_six M p 1 ltac:(lia)BP)as BP6.
 pose proof(source_numf_bound_to_six M qs 2 ltac:(lia)(source_shift_bound M q qs(code_numeral M 1)BQ HQS))as BQS6.
 assert(BE:source_bounded M(code_numeral M(sf_make SFEqual 0 1))(code_numeral M 6)).
 { apply(proj2(source_bounded_accept_atom M SFEqual(zeroM M)(code_numeral M 1)_(code_numeral M 6)(or_intror eq_refl)(sf_make_numeral M SFEqual 0 1))).
   split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel,coding_zero_lt_succ]. }
 assert(BM:source_bounded M(numf_distinct_member M reverse)(code_numeral M 6)).
 { unfold numf_distinct_member. apply(proj2(source_bounded_accept_atom M SFMember
   (code_numeral M(if reverse then 1 else 0))(code_numeral M(if reverse then 0 else 1))_
   (code_numeral M 6)(or_introl eq_refl)(sf_make_numeral M SFMember(if reverse then 1 else 0)(if reverse then 0 else 1)))).
   destruct reverse;split;try apply coding_zero_lt_succ;apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 exact(source_zfr_numf_distinct_composition M reverse p qs _ _ neg inner out mi ml fact(code_numeral M 6)
  BP6 BQS6 BM BE HN HI HO HMI HML HF PM PF).
Qed.
Theorem source_zfr_numf_distinct_canonical M k l p q out:k<>l ->source_numf M k p ->source_numf M l q ->
 source_numf_distinct_recipe M p q(zeroM M)(code_numeral M 1)out ->source_zfr_provable M out.
Proof.
 intros HNE HP HQ HO.
 destruct(@Peano.trichotomy(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)k l)as[HL|[E|HR]].
 - exact(source_zfr_numf_distinct_ordered M false k l p q out HL HP HQ HO).
 - contradiction.
 - exact(source_zfr_numf_distinct_ordered M true k l p q out HR HP HQ HO).
Qed.
Print Assumptions source_zfr_numf_distinct_ordered.
Print Assumptions source_zfr_numf_distinct_canonical.
