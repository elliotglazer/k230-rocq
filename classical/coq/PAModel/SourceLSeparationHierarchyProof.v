(** The actual hierarchy law discharges the carrier-transitivity premise
    of the L-Separation witness. Only ordinary definability and reflection
    source proofs remain as the varying mathematical inputs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceTraceBounds NumericalContexts NumericalContextRenaming NumericalSourceFull
  ContextCombination SourceProofWeakening SourceContextTransport SourceClosedContextShift
  SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceFiniteCutoffShift SourceRelativization SourceSetRelativization
  SourceLDefinableProfile SourceLSeparationCarrierShell SourceLSeparationPsiSProof SourceLSeparationTransitiveContext
  SourceOrdinalPredicate SourceHierarchySyntax NumericalInstantiation SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_full_L_psiS_hierarchy_separation M phi psi matrix lp sp defex allr allt out count
    b c n u v d ordinal level member :
  source_bounded M phi(succM M count) ->source_l_psiS M phi psi ->source_cutoff_shift_thrice M phi matrix ->
  source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
  source_L_definable_profile M psi defex ->
  code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive allt ->
  code_relation M(L_definable_profile_environment lp(source_L_domain_code M))(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
  context_bounded M b c n(succM M(succM M count)) ->context_shift M b c n u v ->
  numerical_instantiation M(source_ordinal_predicate_code M)d ordinal ->
  source_LL_instance M d(code_numeral M 1)level ->sf_relation M SFMember(code_numeral M 2)(code_numeral M 1)member ->
  source_full_prv M b c n defex ->source_full_prv M u v n allr ->
  source_full_prv M u v n ordinal ->source_full_prv M u v n level ->source_full_prv M u v n member ->
  exists ab ac an ub uc un,
    source_zfr_context M ab ac an /\context_union M ab ac an b c n ub uc un /\source_full_prv M ub uc un out.
Proof.
  intros HP HPsi HMatrix HLP HSP HDef HRef HTrans HOut HC HS HO HL HM PDef PRef PO PL PM.
  pose proof(context_shift_preserves_bound M b c n u v(succM M(succM M count))HS HC)as HSC.
  destruct(source_full_L_carrier_transitive_context M u v n(succM M(succM M(succM M count)))
    d ordinal level member allt HSC HO HL HM HTrans PO PL PM)
    as(ab&ac&an&tb&tc&tn&HAC&HTransUnion&PTrans).
  destruct(context_union_total M ab ac an b c n)as(ub&uc&un&HUnion).
  pose proof(context_union_left M ab ac an b c n ub uc un HUnion)as HLeft.
  pose proof(context_union_right M ab ac an b c n ub uc un HUnion)as HRight.
  pose proof(source_zfr_context_closed M ab ac an HAC)as HAClosed.
  pose proof(context_bounded_monotone M ab ac an(zeroM M)(succM M(succM M count))
    HAClosed(coding_zero_lt_succ M(succM M(succM M count))))as HAB.
  pose proof(source_context_union_bounded M ab ac an b c n ub uc un(succM M(succM M count))HUnion HAB HC)as HUC.
  destruct(context_shift_total M ub uc un)as(sb&sc&HUS).
  pose proof(context_shift_preserves_bound M ub uc un sb sc(succM M(succM M count))HUS HUC)as HUSC.
  pose proof(source_context_included_shift M b c n ub uc un u v sb sc HRight HS HUS)as HShiftRight.
  pose proof(source_context_included_shift M ab ac an ub uc un ab ac sb sc HLeft
    (source_closed_context_shift_self M ab ac an HAClosed)HUS)as HShiftLeft.
  assert(HTransIncluded:context_included M tb tc tn sb sc un).
  { intros f HF. apply(proj1(proj2 HTransUnion f))in HF.
    destruct HF as[HF|HF];[exact(HShiftLeft f HF)|exact(HShiftRight f HF)]. }
  pose proof(source_full_prv_weaken_bounded M b c n ub uc un defex(succM M(succM M count))PDef HRight HUC)as PDef'.
  pose proof(source_full_prv_weaken_bounded M u v n sb sc un allr(succM M(succM M(succM M count)))PRef HShiftRight HUSC)as PRef'.
  pose proof(source_full_prv_weaken_bounded M tb tc tn sb sc un allt(succM M(succM M(succM M count)))PTrans HTransIncluded HUSC)as PTrans'.
  exists ab,ac,an,ub,uc,un. split;[exact HAC|]. split;[exact HUnion|].
  exact(source_full_L_psiS_carrier_separation M phi psi matrix lp sp defex allr allt out count ub uc un sb sc
    HP HPsi HMatrix HLP HSP HDef HRef HTrans HOut HUC HUS PDef' PRef' PTrans').
Qed.

Print Assumptions source_full_L_psiS_hierarchy_separation.
