(** Guard-close an actual image proof obtained in a domain table plus
    closed ZFR axioms, retaining any extra closed axiom context its macro used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
 SourceTraceBounds SourceClosedContextShift SourceProofWeakening ContextCombination SourceDomainContexts SourceGuardedDomainClosure
 SourceRelativization NumericalSetClosure SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_domain_prefix_from_union M domain count body relative f rf
 gb gc gn db dc ub uc un ab ac an wb wc wn:
 source_bounded M domain(code_numeral M 1) ->source_bounded M body count ->
 all_prefix M count body f ->source_relativization M domain body relative ->source_relativization M domain f rf ->
 source_zfr_context M gb gc gn ->source_domain_context M domain count db dc ->
 context_union M gb gc gn db dc count ub uc un ->source_zfr_context M ab ac an ->
 context_union M ab ac an ub uc un wb wc wn ->source_full_prv M wb wc wn relative ->source_zfr_provable M rf.
Proof.
 intros HD HB HP HR HF HG HTable HU HA HW P.
 destruct(context_union_total M ab ac an gb gc gn)as(xb&xc&xn&HX).
 assert(HZ:source_zfr_context M xb xc xn).
 { intros a HAx. apply(proj1(proj2 HX a))in HAx. destruct HAx as[HAx|HAx];[exact(HA a HAx)|exact(HG a HAx)]. }
 destruct(context_union_total M xb xc xn db dc count)as(yb&yc&yn&HY).
 assert(BY:context_bounded M yb yc yn count).
 { apply(source_context_union_bounded M xb xc xn db dc count yb yc yn count HY).
   - exact(context_bounded_monotone M xb xc xn(zeroM M)count(source_zfr_context_closed M xb xc xn HZ)(coding_zero_lt_succ M count)).
   - exact(source_domain_context_bounded M domain count db dc HD HTable). }
 assert(HInclude:context_included M wb wc wn yb yc yn).
 { intros a HAx. apply(proj1(proj2 HW a))in HAx. apply(proj2(proj2 HY a)).
   destruct HAx as[HAx|HAx].
   - left. apply(proj2(proj2 HX a)). now left.
   - apply(proj1(proj2 HU a))in HAx. destruct HAx as[HAx|HAx];[left;apply(proj2(proj2 HX a));now right|now right]. }
 pose proof(source_full_prv_weaken_bounded M wb wc wn yb yc yn relative count P HInclude BY)as PRelative.
 exists xb,xc,xn. split;[exact HZ|].
 exact(source_full_guarded_domain_close M domain xb xc xn(source_zfr_context_closed M xb xc xn HZ)HD count
  body relative f rf db dc yb yc yn HB HP HR HF HTable HY PRelative).
Qed.
Print Assumptions source_zfr_domain_prefix_from_union.
