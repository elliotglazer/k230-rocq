(** Actual ExE across a fixed finite implication telescope. The witness
    implication is a real numerical proof, with all shifts checked. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull SourceTraceBounds SourceQuantifierRules
 SourceFiniteTelescope SourceFiniteTelescopeQuantifier SourceProofWeakening SourceClosedContextShift SourceContextTransport
 SourceContextProofHelpers SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_finite_telescope_exists M A AS body ex target shifted oldLaw newLaw k:
 (forall a,In a A ->source_bounded M a k) ->source_bounded M ex k ->source_bounded M target k ->
 Forall2(source_formula_shift M)A AS ->sf_relation M SFEx body(zeroM M)ex ->source_formula_shift M target shifted ->
 source_finite_telescope M(AS++[body])shifted oldLaw ->source_finite_telescope M(A++[ex])target newLaw ->
 source_zfr_provable M oldLaw ->source_zfr_provable M newLaw.
Proof.
 intros BA BE BT HShift HEx HTarget HOld HNew(cb&cc&cn&HClosed&POld).
 pose proof(source_zfr_context_closed M cb cc cn HClosed)as BClosed.
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)k BClosed(coding_zero_lt_succ M k))as BC.
 exists cb,cc,cn. split;[exact HClosed|].
 apply(source_full_finite_telescope M(A++[ex])target newLaw k).
 - intros a HA. apply in_app_or in HA. destruct HA as[HA|[<-|[]]];[exact(BA a HA)|exact BE].
 - exact BT.
 - exact HNew.
 - exact BC.
 - intros b c n BContext Included Premises.
   assert(PEx:source_full_prv M b c n ex).
   { apply Premises,in_or_app. right. now left. }
   assert(PA:forall a,In a A ->source_full_prv M b c n a).
   { intros a HA. apply Premises,in_or_app. now left. }
   destruct(context_shift_total M b c n)as(sb&sc&HS).
   pose proof(context_shift_preserves_bound M b c n sb sc k HS BContext)as BS.
   pose proof(proj1(source_bounded_accept_unary M SFEx body ex k(or_intror eq_refl)HEx)BE)as BBody.
   destruct(environment_cons_total M sb sc n body)as(ub&uc&un&HCons).
   pose proof(proj2(context_bounded_cons M sb sc n body ub uc un(succM M k)HCons)(conj BBody BS))as BU.
   assert(InShift:context_included M cb cc cn sb sc n).
   { exact(source_context_included_shift M cb cc cn b c n cb cc sb sc Included(source_closed_context_shift_self M cb cc cn BClosed)HS). }
   assert(InBranch:context_included M cb cc cn ub uc un).
   { intros ax HAx. apply(proj2(context_member_cons M sb sc n body ub uc un ax HCons)). right. exact(InShift ax HAx). }
   pose proof(source_full_prv_weaken_bounded M cb cc cn ub uc un oldLaw(succM M k)POld InBranch BU)as POldBranch.
   pose proof(source_full_shifted_finite_hypotheses M A AS b c n sb sc HShift HS PA)as PAS.
   assert(PremisesBranch:forall a,In a(AS++[body]) ->source_full_prv M ub uc un a).
   { intros a HA. apply in_app_or in HA. destruct HA as[HA|[<-|[]]].
     - exact(source_full_cons_weaken M sb sc n body ub uc un(succM M k)a HCons BU(PAS a HA)).
     - exact(source_full_cons_head M sb sc n body ub uc un(succM M k)HCons BBody BU). }
   pose proof(source_full_finite_telescope_apply M(AS++[body])shifted oldLaw HOld ub uc un POldBranch PremisesBranch)as PShifted.
   exact(full_source_ExE M b c n body ex target shifted sb sc ub uc un(ex_intro _ k(conj BT BContext))PEx PShifted HEx HS HCons HTarget).
Qed.
Print Assumptions source_zfr_finite_telescope_exists.
