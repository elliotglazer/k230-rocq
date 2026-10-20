(** Remove the external hierarchy-carrier witness by literal source ExE.
    The branch consumes the ordinary definability and reflection proofs; the
    result is the canonical witness with no carrier parameter. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceBounded SchemaConstructorBounds SchemaRenamingDescriptors SchemaRenamingBounds SourceRelativization SourceRelativizationBounds
  SourceSetRelativization SourceLFixed SourceLMatrixRecipes SourceD0Recipe SourceFiniteCutoffShift
  SourceLDefinableProfile SourceLSeparationCarrierShell SourceLSeparationWitnessShift SourceLSeparationSchemaShift SourceLSeparationPsiSProof
  NumericalContexts NumericalContextRenaming NumericalEnvironments NumericalSourceFull SourceQuantifierRules.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Theorem source_lsep_canonical_witness_bounded M domain lp witness count :
  source_bounded M domain(code_numeral M 1) ->
  source_bounded M lp(succM M(succM M(succM M count))) ->
  code_relation M(L_definable_profile_environment lp domain)
    (E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
  source_bounded M witness(succM M count).
Proof.
  intros HD HLP HGraph.
  assert(HD2:source_bounded M domain(succM M(succM M count))).
  { exact(sr_domain_bound_succ M domain(succM M count)HD). }
  assert(HD3:source_bounded M domain(succM M(succM M(succM M count)))).
  { exact(sr_domain_bound_succ M domain(succM M(succM M count))HD). }
  assert(HB:schema_expression_bound M(L_definable_profile_environment lp domain)
    (E_L_canonical_separation_witness(CEvar 1)(CEvar 0))(succM M count)).
  { unfold E_L_canonical_separation_witness,E_L_indexed_separation,E_sf_iff.
    repeat schema_constructor_bound;try schema_small_index;assumption. }
  exact(HB witness HGraph).
Qed.

Theorem source_full_L_psiS_carrier_elimination M phi psi body matrix rp lp sp defex allr allt witness carrier
    count b c n sb sc eb ec en tb tc exbody ex :
  source_bounded M phi(succM M count) ->source_l_psiS M phi psi ->
  schema_renaming M SepBody phi body ->source_cutoff_shift_thrice M phi matrix ->
  source_relativization M(source_L_domain_code M)body rp ->
  source_relativization M(source_L_domain_code M)matrix lp ->
  source_set_relativization M(code_numeral M 2)matrix sp ->source_L_definable_profile M psi defex ->
  code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive allt ->
  code_relation M(L_definable_profile_environment rp(source_L_domain_code M))
    (E_L_canonical_separation_witness(CEvar 1)(CEvar 0))witness ->
  code_relation M(L_definable_profile_environment lp(source_L_domain_code M))
    (E_L_carrier_separation(CEvar 1)(CEvar 0))carrier ->
  context_bounded M b c n(succM M count) ->context_shift M b c n sb sc ->
  environment_cons M sb sc n exbody eb ec en ->context_bounded M eb ec en(succM M(succM M count)) ->
  context_shift M eb ec en tb tc ->sf_relation M SFEx exbody(zeroM M)ex ->
  source_full_prv M b c n ex ->source_full_prv M eb ec en defex ->
  source_full_prv M tb tc en allr ->source_full_prv M tb tc en allt ->
  source_full_prv M b c n witness.
Proof.
  intros HP HPsi HBody HMatrix HRP HLP HSP HDef HRef HTrans HWitness HCarrier
    HC HS HCons HBranch HT HEx PEx PDef PRef PTrans.
  pose proof(source_full_L_psiS_carrier_separation M phi psi matrix lp sp defex allr allt carrier count
    eb ec en tb tc HP HPsi HMatrix HLP HSP HDef HRef HTrans HCarrier HBranch HT PDef PRef PTrans) as PCarrier.
  pose proof(source_L_SepBody_witness_carrier_shift M(source_L_domain_code M)phi body matrix rp lp witness carrier count
    (numerical_L_domain_bounded M)HP HBody HMatrix HRP HLP HWitness HCarrier) as HWitnessShift.
  pose proof(source_relativization_preserves_bound M body(source_L_domain_code M)
    (succM M(succM M(succM M count)))rp(numerical_L_domain_bounded M)
    (schema_separation_bound M phi body count HP HBody)HRP) as BRP.
  pose proof(source_lsep_canonical_witness_bounded M(source_L_domain_code M)rp witness count
    (numerical_L_domain_bounded M)BRP HWitness) as BWitness.
  exact(full_source_ExE M b c n exbody ex witness carrier sb sc eb ec en
    (ex_intro _ (succM M count)(conj BWitness HC))PEx PCarrier HEx HS HCons HWitnessShift).
Qed.

Print Assumptions source_lsep_canonical_witness_bounded.
Print Assumptions source_full_L_psiS_carrier_elimination.
