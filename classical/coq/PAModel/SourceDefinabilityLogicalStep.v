(** Actual numerical existential proof construction for the NumF successor.
    The matrix is an arbitrary internal formula bounded by one free index.
    The only mathematical premise is an actual successor-existence proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 SetFormulaCodes SourceBounded SourceBoundMonotone SourceQuantifierRules
 NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceSubstitutionIdentity
 SourceSubstitutionRenaming SourceShiftSpecialization NumericalRenamingMaps NumericalRenaming
 NumericalContexts NumericalEnvironments NumericalContextRenaming SourceClosedContextShift SourceClosedShift
 SourceContextProofHelpers SourceContextTransport SourceProofWeakening SourceSequents SourceTraceBounds
 SourceInstantiationConstructors NumericalSourceFull SourceUpperProofHelpers SourceRenamingBounds.
Unset Implicit Arguments.

Lemma source_unit_instantiation_self M f :source_bounded M f(code_numeral M 1) ->
 numerical_instantiation M f(zeroM M) f.
Proof.
 intro HF. destruct(substitution_singleton_total M(zeroM M))as(b&c&HH&HT).
 exists b,c. split;[exact HH|]. apply(numerical_substitution_identity_on_bound M f b c
  (code_numeral M 1)(zeroM M)(code_numeral M 1) HF).
 intros i HI. apply coding_lt_succ_cases in HI. destruct HI as[HI | EI].
 - exfalso. exact(coding_not_lt_zero M i HI).
 - subst i. exact HH.
Qed.
Lemma source_unit_instantiation_shift M f shifted :source_bounded M f(code_numeral M 1) ->
 source_formula_shift M f shifted ->numerical_instantiation M f(code_numeral M 1) shifted.
Proof.
 intros HF HR. destruct(substitution_singleton_total M(code_numeral M 1))as(b&c&HH&HT).
 exists b,c. split;[exact HH|].
 assert(HI:numerical_substitution M f(zeroM M)(zeroM M)(zeroM M)(zeroM M) f).
 { apply(numerical_substitution_identity_on_bound M f _ _ _ _ (code_numeral M 1) HF).
   intros i _. apply source_empty_substitution_lookup. }
 apply(numerical_substitution_then_renaming M f(code_numeral M 1)
  (zeroM M)(zeroM M)(zeroM M)(zeroM M)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  b c(code_numeral M 1)(zeroM M) f shifted HF HI HR).
 intros i j v HBound HSub HMap.
 apply coding_lt_succ_cases in HBound. destruct HBound as[HBad|EI].
 - exfalso. exact(coding_not_lt_zero M i HBad).
 - subst i. assert(EJ:j=zeroM M).
   { eapply substitution_lookup_functional;[exact HSub|apply source_empty_substitution_lookup]. }
   subst j. apply context_shift_lookup in HMap. subst v. exact HH.
Qed.

Theorem source_full_unit_exists_successor M b c n f shifted exf s01 s10 exs pair next exnext pairinst :
 context_bounded M b c n(zeroM M) ->source_bounded M f(code_numeral M 1) ->
 source_formula_shift M f shifted ->
 source_bounded M s01(code_numeral M 2) ->source_bounded M s10(code_numeral M 2) ->
 sf_relation M SFEx f(zeroM M) exf ->sf_relation M SFEx s10(zeroM M) exs ->
 sf_relation M SFAnd f s01 pair ->sf_relation M SFEx pair(zeroM M) next ->
 sf_relation M SFEx next(zeroM M) exnext ->
 numerical_instantiation M s01(code_numeral M 1) s10 ->
 sf_relation M SFAnd shifted s10 pairinst ->
 source_full_prv M b c n exf ->source_full_prv M b c n exs ->
 source_full_prv M b c n exnext.
Proof.
 intros HC HF HShift HS01 HS10 HExF HExS HPair HNext HExNext HSI HPairInst PF PS.
 assert(HF2:source_bounded M shifted(code_numeral M 2)).
 { apply(numerical_renaming_preserves_bound M f _ _ _ _ shifted (code_numeral M 1)(code_numeral M 2) HF HShift).
   intros i j HI HJ. apply context_shift_lookup in HJ. subst j. apply coding_lt_succ_cancel. exact HI. }
 assert(HBPair:source_bounded M pair(code_numeral M 2)).
 { apply(proj2(source_bounded_accept_binary M SFAnd f s01 pair(code_numeral M 2)(or_introl eq_refl) HPair)).
   split;[|exact HS01]. apply(source_bounded_monotone M f(code_numeral M 1)(code_numeral M 2) HF).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(HNext1:source_bounded M next(code_numeral M 1)).
 { exact(proj2(source_bounded_accept_unary M SFEx pair next(code_numeral M 1)(or_intror eq_refl) HNext) HBPair). }
 assert(HOut:source_bounded M exnext(zeroM M)).
 { exact(proj2(source_bounded_accept_unary M SFEx next exnext(zeroM M)(or_intror eq_refl) HExNext) HNext1). }
 destruct(environment_cons_total M b c n f)as(b1&c1&n1&H1).
 destruct(environment_cons_total M b c n shifted)as(b2&c2&n2&H2).
 assert(En:n2=n1)by(rewrite(proj1 H1),(proj1 H2);reflexivity). subst n2.
 destruct(environment_cons_total M b2 c2 n1 s10)as(b3&c3&n3&H3).
 assert(C1:context_bounded M b1 c1 n1(code_numeral M 1)).
 { apply(proj2(context_bounded_cons M b c n f b1 c1 n1(code_numeral M 1) H1)).
   split;[exact HF|]. exact(context_bounded_monotone M b c n(zeroM M)(code_numeral M 1) HC(coding_zero_lt_succ M(code_numeral M 1))). }
 assert(C2:context_bounded M b2 c2 n1(code_numeral M 2)).
 { apply(proj2(context_bounded_cons M b c n shifted b2 c2 n1(code_numeral M 2) H2)).
   split;[exact HF2|]. exact(context_bounded_monotone M b c n(zeroM M)(code_numeral M 2) HC(coding_zero_lt_succ M(code_numeral M 2))). }
 assert(C3:context_bounded M b3 c3 n3(code_numeral M 2)).
 { apply(proj2(context_bounded_cons M b2 c2 n1 s10 b3 c3 n3(code_numeral M 2) H3));auto. }
 pose proof(source_full_cons_head M b c n shifted b2 c2 n1(code_numeral M 2) H2 HF2 C2)as PShift.
 pose proof(source_full_cons_weaken M b2 c2 n1 s10 b3 c3 n3(code_numeral M 2) shifted H3 C3 PShift)as PShift3.
 pose proof(source_full_cons_head M b2 c2 n1 s10 b3 c3 n3(code_numeral M 2) H3 HS10 C3)as PS10.
 pose proof(source_full_conjunction M b3 c3 n3 shifted s10 pairinst HPairInst PShift3 PS10)as PPair.
 assert(HI:numerical_instantiation M pair(code_numeral M 1) pairinst).
 { exact(source_instantiation_binary M SFAnd f s01 pair(code_numeral M 1) shifted s10 pairinst
     (or_introl eq_refl) HPair(source_unit_instantiation_shift M f shifted HF HShift) HSI HPairInst). }
 assert(PNext:source_full_prv M b3 c3 n3 next).
 { apply(full_source_ExI M b3 c3 n3 pair next(code_numeral M 1) pairinst);[|exact PPair|exact HNext|exact HI].
   exists(code_numeral M 2). split;[|exact C3].
   apply(source_bounded_monotone M next(code_numeral M 1)(code_numeral M 2) HNext1).
   apply coding_lt_succ_cancel,coding_zero_lt_succ. }
 assert(POut3:source_full_prv M b3 c3 n3 exnext).
 { apply(full_source_ExI M b3 c3 n3 next exnext(zeroM M) next);[|exact PNext|exact HExNext|].
   - exists(code_numeral M 2). split;[|exact C3].
     apply(source_bounded_monotone M exnext(zeroM M)(code_numeral M 2) HOut). apply coding_zero_lt_succ.
   - exact(source_unit_instantiation_self M next HNext1). }
 assert(HShiftContext:context_shift M b1 c1 n1 b2 c2).
 { exact(context_renaming_cons M b c n(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
     b c f shifted b1 c1 n1 b2 c2(source_closed_context_shift_self M b c n HC) HShift H1 H2). }
 assert(POut1:source_full_prv M b1 c1 n1 exnext).
 { apply(full_source_ExE M b1 c1 n1 s10 exs exnext exnext b2 c2 b3 c3 n3);try assumption.
   - exists(code_numeral M 1). split;[|exact C1].
     apply(source_bounded_monotone M exnext(zeroM M)(code_numeral M 1) HOut). apply coding_zero_lt_succ.
   - exact(source_full_cons_weaken M b c n f b1 c1 n1(code_numeral M 1) exs H1 C1 PS).
   - apply source_closed_shift_self. exact HOut. }
 apply(full_source_ExE M b c n f exf exnext exnext b c b1 c1 n1);try assumption.
 - exists(zeroM M). auto.
 - exact(source_closed_context_shift_self M b c n HC).
 - apply source_closed_shift_self. exact HOut.
Qed.
Print Assumptions source_unit_instantiation_self.
Print Assumptions source_unit_instantiation_shift.
Print Assumptions source_full_unit_exists_successor.
