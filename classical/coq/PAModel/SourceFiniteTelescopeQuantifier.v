(** Pull a genuine universal rule across a fixed finite implication macro.
    Formula names and the matrices may be nonstandard model elements. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalContextRenaming NumericalSourceFull SourceTraceBounds SourceQuantifierRules
 SourceFiniteTelescope SourceProofRenaming SourceProofWeakening SourceClosedContextShift SourceContextTransport SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_finite_telescope_prefix M A B middle target out:
 source_finite_telescope M A middle out ->source_finite_telescope M B target middle ->
 source_finite_telescope M(A++B)target out.
Proof.
 revert out. induction A as[|a A IH];intros out HA HB.
 - change(out=middle)in HA. subst out. exact HB.
 - destruct HA as(inner&HI&HO). exists inner. split;[exact(IH inner HI HB)|exact HO].
Qed.
Theorem source_full_shifted_finite_hypotheses M A AS cb cc cn sb sc:
 Forall2(source_formula_shift M)A AS ->context_shift M cb cc cn sb sc ->
 (forall a,In a A ->source_full_prv M cb cc cn a) ->forall a,In a AS ->source_full_prv M sb sc cn a.
Proof.
 intros HR HC. induction HR;intros Premises a HA;[contradiction|].
 destruct HA as[<-|HA].
 - exact(source_full_prv_renaming M cb cc cn x(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)sb sc y
   (Premises x(or_introl eq_refl))HC H).
 - exact(IHHR(fun f HF=>Premises f(or_intror HF))a HA).
Qed.
Theorem source_zfr_finite_telescope_all M A AS matrix all oldLaw newLaw k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M matrix(succM M k) ->
 Forall2(source_formula_shift M)A AS ->sf_relation M SFAll matrix(zeroM M)all ->
 source_finite_telescope M AS matrix oldLaw ->source_finite_telescope M A all newLaw ->
 source_zfr_provable M oldLaw ->source_zfr_provable M newLaw.
Proof.
 intros BA BM HShift HAll HOld HNew(cb&cc&cn&HClosed&POld).
 pose proof(source_zfr_context_closed M cb cc cn HClosed)as BClosed.
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)k BClosed(coding_zero_lt_succ M k))as BC.
 pose proof(proj2(source_bounded_accept_unary M SFAll matrix all k(or_introl eq_refl)HAll)BM)as BAll.
 exists cb,cc,cn. split;[exact HClosed|].
 apply(source_full_finite_telescope M A all newLaw k BA BAll HNew cb cc cn BC).
 intros b c n BContext Included Premises.
 destruct(context_shift_total M b c n)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b c n sb sc k HS BContext)as BS.
 assert(InShift:context_included M cb cc cn sb sc n).
 { exact(source_context_included_shift M cb cc cn b c n cb cc sb sc Included(source_closed_context_shift_self M cb cc cn BClosed)HS). }
 pose proof(source_full_prv_weaken_bounded M cb cc cn sb sc n oldLaw(succM M k)POld InShift BS)as POldShift.
 pose proof(source_full_shifted_finite_hypotheses M A AS b c n sb sc HShift HS Premises)as ShiftedPremises.
 pose proof(source_full_finite_telescope_apply M AS matrix oldLaw HOld sb sc n POldShift ShiftedPremises)as PPoint.
 exact(full_source_AllI M b c n matrix all sb sc(ex_intro _ k(conj BAll BContext))PPoint HS HAll).
Qed.
Print Assumptions source_finite_telescope_prefix.
Print Assumptions source_full_shifted_finite_hypotheses.
Print Assumptions source_zfr_finite_telescope_all.
