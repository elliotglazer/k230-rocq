(** Connect the exact pinned psiS/definable recipes to the actual guarded
    Separation witness, with an arbitrary internally coded predicate. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
  SourceFiniteCutoffShift SourceD0Recipe SourceQfFunctionality SourceLFixed SourceLMatrixRecipes
  SourceRelativization SourceSetRelativization SourceSetRelativizationFunctionality
  SourceLDefinableProfile SourceLSeparationDefinableNormalization SourceLSeparationCarrierShell SourceLSeparationCarrierProof
  NumericalContexts NumericalContextRenaming NumericalSourceFull.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_full_L_psiS_carrier_separation M phi psi matrix lp sp defex allr allt out count b c n u v :
  source_bounded M phi(succM M count) ->source_l_psiS M phi psi ->source_cutoff_shift_thrice M phi matrix ->
  source_relativization M(source_L_domain_code M)matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
  source_L_definable_profile M psi defex ->
  code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive allt ->
  code_relation M(L_definable_profile_environment lp(source_L_domain_code M))(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
  context_bounded M b c n(succM M(succM M count)) ->context_shift M b c n u v ->
  source_full_prv M b c n defex ->source_full_prv M u v n allr ->source_full_prv M u v n allt ->
  source_full_prv M b c n out.
Proof.
  intros HP HPsi HMatrix HLP HSP HDef HRef HTrans HOut HC HShift PDef PRef PTrans.
  destruct(source_L_psiS_definable_normalization M(source_L_domain_code M)phi psi defex HPsi HDef)
    as(first&second&matrix'&za&selected&sp'&H1&H2&H3&HZA&HSP'&HSelected&HDefGraph).
  assert(HMatrix':source_cutoff_shift_thrice M phi matrix').
  { exists first,second. repeat split;assumption. }
  pose proof(source_cutoff_shift_thrice_functional M phi matrix matrix' HMatrix HMatrix') as E. subst matrix'.
  pose proof(source_set_relativization_functional M matrix(code_numeral M 2)sp sp' HSP HSP') as E. subst sp'.
  pose proof(source_lsep_selected_profile_shell M(source_L_domain_code M)za sp selected defex HZA HSelected HDefGraph) as HShell.
  assert(HThree:coding_lt M(code_numeral M 3)(succM M(succM M(succM M(succM M count))))).
  { change(coding_lt M(succM M(succM M(succM M(zeroM M))))(succM M(succM M(succM M(succM M count))))).
    do 3 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
  pose proof(source_L_definable_profile_bounded M(succM M count)psi defex
    (source_l_psiS_bounded M phi psi count HP HPsi)HDef) as BDef.
  exact(source_full_L_separation_carrier_witness M(source_L_domain_code M)matrix lp sp defex allr allt out
    (succM M(succM M count))b c n u v(numerical_L_domain_bounded M)
    (source_cutoff_shift_thrice_bounded M phi matrix count HP HMatrix)HThree HLP HSP HShell
    HRef HTrans HOut HC BDef HShift PDef PRef PTrans).
Qed.
Print Assumptions source_full_L_psiS_carrier_separation.
