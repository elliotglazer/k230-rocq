(** Open an internally finite guarded universal prefix under its exact
    domain table, using actual source AllE/MP and arithmetic count induction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs NumericalContexts NumericalEnvironments NumericalContextRenaming
 SourceBounded SourceBoundMonotone SourceTraceBounds SetFormulaCodes SourceQuantifierRules NumericalSourceFull NumericalSetClosure
 SourceProofWeakening SourceDomainContexts SourceDomainDischarge ContextCombination ContextUnionRenaming SourceClosedContextShift
 SourceRelativization SourceRelativizationRules SourceRelativizationFunctionality SourceRelativizationBounds SourceGuardedDomainClosure
 SourceUniversalPropositional SourceDerivedRules SourceContextProofHelpers SourceLeastOrdinalWitness SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_guarded_domain_open_at M domain gb gc gn k:=
 forall body relative result rresult db dc ub uc ul,
 source_bounded M body k ->all_prefix M k body result ->
 source_relativization M domain body relative ->source_relativization M domain result rresult ->
 source_domain_context M domain k db dc ->context_union M gb gc gn db dc k ub uc ul ->
 source_full_prv M gb gc gn rresult ->source_full_prv M ub uc ul relative.
Definition source_guarded_domain_open_formula:form:=
 ∀∀∀∀∀∀∀∀∀(source_bounded_accept_formula $8 $9 →all_prefix_formula $9 $8 $6 →
 source_relativization_formula $10 $8 $7 →source_relativization_formula $10 $6 $5 →
 source_domain_context_formula $10 $9 $4 $3 →context_union_formula $11 $12 $13 $4 $3 $9 $2 $1 $0 →
 source_full_prv_formula $11 $12 $13 $5 →source_full_prv_formula $2 $1 $0 $7).
Local Opaque holds source_bounded_accept_formula all_prefix_formula source_relativization_formula
 source_domain_context_formula context_union_formula source_full_prv_formula.
Lemma source_guarded_domain_open_definable M domain gb gc gn:Definable1 M(source_guarded_domain_open_at M domain gb gc gn).
Proof.
 exists source_guarded_domain_open_formula,(domain .:gb .:gc .:gn .:fun _=>zeroM M). intro k.
 unfold source_guarded_domain_open_formula,source_guarded_domain_open_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite all_prefix_formula_correct.
 setoid_rewrite source_relativization_formula_correct. setoid_rewrite source_domain_context_formula_correct.
 setoid_rewrite context_union_formula_correct. setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.
Theorem source_full_guarded_domain_open M domain gb gc gn:
 context_bounded M gb gc gn(zeroM M) ->source_bounded M domain(code_numeral M 1) ->
 forall k,source_guarded_domain_open_at M domain gb gc gn k.
Proof.
 intros HClosed HD. apply(definable_induction M(source_guarded_domain_open_at M domain gb gc gn)
  (source_guarded_domain_open_definable M domain gb gc gn)).
 - intros body relative result rresult db dc ub uc ul HB HP HR HF HT HU P.
   apply all_prefix_zero_forward in HP. subst result.
   assert(E:rresult=relative)by(eapply source_relativization_functional;eassumption). subst rresult.
   apply(source_full_prv_weaken_bounded M gb gc gn ub uc ul relative(zeroM M)P(context_union_left M gb gc gn db dc(zeroM M)ub uc ul HU)).
   apply(source_context_union_bounded M gb gc gn db dc(zeroM M)ub uc ul(zeroM M)HU HClosed).
   exact(source_domain_context_bounded M domain(zeroM M)db dc HD HT).
 - intros k IH body relative result rresult db dc ub uc ul HB HP HR HF HT HU P.
   destruct(sf_relation_total M SFAll body(zeroM M))as(all&HAll).
   destruct(source_relativization_total M domain all)as(rall&HRAll).
   destruct(source_relativization_quantifier_inv M domain true body all rall HAll HRAll)as(rbody&HRBody&guard&HGuard&HOutput).
   assert(E:rbody=relative)by(eapply source_relativization_functional;eassumption). subst rbody.
   destruct(source_domain_context_total M domain k)as(tb&tc&HTable).
   destruct(context_union_total M gb gc gn tb tc k)as(vb&vc&vl&HUnion).
   pose proof(IH all rall result rresult tb tc vb vc vl
    (proj2(source_bounded_accept_unary M SFAll body all k(or_introl eq_refl)HAll)HB)
    (all_prefix_remove_first M k body all result HAll HP)HRAll HF HTable HUnion P)as PAll.
   destruct(context_shift_total M tb tc k)as(tsb&tsc&HTableShift).
   destruct(context_shift_total M vb vc vl)as(vsb&vsc&HUnionShift).
   destruct(environment_cons_total M tsb tsc k domain)as(tb'&tc'&tk'&HTableCons).
   assert(ET:tk'=succM M k)by exact(proj1 HTableCons). subst tk'.
   destruct(environment_cons_total M vsb vsc vl domain)as(wb&wc&wl&HUnionCons).
   pose proof(source_domain_context_cons_shift M domain k tb tc tsb tsc tb' tc'(succM M k)HD HTable HTableShift HTableCons)as HCanonical.
   pose proof(context_union_renaming M gb gc gn tb tc k vb vc vl(zeroM M)(zeroM M)(zeroM M)(succM M(zeroM M))
    gb gc tsb tsc vsb vsc HUnion(source_closed_context_shift_self M gb gc gn HClosed)HTableShift HUnionShift)as HShiftedUnion.
   pose proof(context_union_cons_right M gb gc gn tsb tsc k vsb vsc vl domain tb' tc'(succM M k)wb wc wl HShiftedUnion HTableCons HUnionCons)as HBranchUnion.
   assert(HC:context_bounded M vb vc vl k).
   { apply(source_context_union_bounded M gb gc gn tb tc k vb vc vl k HUnion).
     - exact(context_bounded_monotone M gb gc gn(zeroM M)k HClosed(coding_zero_lt_succ M k)).
     - exact(source_domain_context_bounded M domain k tb tc HD HTable). }
   pose proof(context_shift_preserves_bound M vb vc vl vsb vsc k HUnionShift HC)as HSC.
   assert(HBC:context_bounded M wb wc wl(succM M k)).
   { apply(proj2(context_bounded_cons M vsb vsc vl domain wb wc wl(succM M k)HUnionCons)).
     exact(conj(sr_domain_bound_succ M domain k HD)HSC). }
   pose proof(source_full_all_shift M vb vc vl guard rall vsb vsc HOutput PAll HUnionShift)as PG.
   pose proof(source_full_cons_weaken M vsb vsc vl domain wb wc wl(succM M k)guard HUnionCons HBC PG)as PG'.
   pose proof(source_full_cons_head M vsb vsc vl domain wb wc wl(succM M k)HUnionCons(sr_domain_bound_succ M domain k HD)HBC)as PD.
   pose proof(source_full_modus_ponens M wb wc wl domain relative guard HGuard PG' PD)as PR.
   assert(HUC:context_bounded M ub uc ul(succM M k)).
   { apply(source_context_union_bounded M gb gc gn db dc(succM M k)ub uc ul(succM M k)HU).
     - exact(context_bounded_monotone M gb gc gn(zeroM M)(succM M k)HClosed(coding_zero_lt_succ M(succM M k))).
     - exact(source_domain_context_bounded M domain(succM M k)db dc HD HT). }
   apply(source_full_prv_weaken_bounded M wb wc wl ub uc ul relative(succM M k)PR);[|exact HUC].
   intros a HA. apply(proj1(proj2 HBranchUnion a))in HA. apply(proj2(proj2 HU a)).
   destruct HA as[HA|HA];[now left|right].
   exact(source_domain_context_representation_included M domain(succM M k)tb' tc' db dc HCanonical HT a HA).
Qed.
Theorem source_zfr_open_relative_prefix M domain count body relative f rf db dc:
 source_bounded M domain(code_numeral M 1) ->source_bounded M body count ->
 all_prefix M count body f ->source_relativization M domain body relative ->source_relativization M domain f rf ->
 source_domain_context M domain count db dc ->source_zfr_provable M rf ->
 exists ab ac an ub uc un,source_zfr_context M ab ac an /\context_union M ab ac an db dc count ub uc un /\source_full_prv M ub uc un relative.
Proof.
 intros HD HB HP HR HF HT(ab&ac&an&HA&P).
 destruct(context_union_total M ab ac an db dc count)as(ub&uc&un&HU).
 exists ab,ac,an,ub,uc,un. split;[exact HA|]. split;[exact HU|].
 exact(source_full_guarded_domain_open M domain ab ac an(source_zfr_context_closed M ab ac an HA)HD count body relative f rf db dc ub uc un HB HP HR HF HT HU P).
Qed.
Print Assumptions source_guarded_domain_open_definable.
Print Assumptions source_full_guarded_domain_open.
Print Assumptions source_zfr_open_relative_prefix.
