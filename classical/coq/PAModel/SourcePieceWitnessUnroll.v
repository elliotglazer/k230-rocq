(** Removing the internally many parameter binders in a genuine unary
    piece-witness closure instance, by actual numerical source deductions. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SourceSubstitutionIdentity SourceSubstitutionBounds
  SourcePieceWitnessUnary SourcePieceWitnessInstance SourceEwAtSyntax SourceEwMonotone SourceEwSubstitution
  SourceBallS SourceBallSSubstitution SourceBallSInverseBounds SourceBallSElimination SourceBallSInstanceMaps
  SourceInternalLifts SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Theorem source_piece_witness_instance_unroll M domain count piece carrier out:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  source_piece_witness_instance M domain count piece carrier out ->
  exists ew,source_ew_at M domain piece(addM M count carrier)ew /\source_ballS M count carrier ew out.
Proof.
  intros HD HP(unary&(ew&HE&HB)&ib&ic&HHead&HOut).
  destruct(source_upn_map_total M count ib ic(code_numeral M 1)(zeroM M))as(ub&uc&HUp).
  destruct(source_upn_map_total M(succM M count)ib ic(code_numeral M 1)(zeroM M))as(ab&ac&HUpA).
  pose proof(source_upn_map_successor_lift M count ib ic(code_numeral M 1)(zeroM M)ub uc ab ac HUp HUpA)as HL.
  assert(HFix:substitution_fixes_bound M ab ac(addM M(succM M count)(code_numeral M 1))
    (addM M(succM M count)(zeroM M))(succM M count)).
  { intros i HI. exact(source_upn_map_head M(succM M count)ib ic(code_numeral M 1)(zeroM M)ab ac i HUpA HI). }
  pose proof(numerical_substitution_identity_on_bound M piece ab ac(addM M(succM M count)(code_numeral M 1))
    (addM M(succM M count)(zeroM M))(succM M count)HP HFix)as HMatrix.
  assert(HMatrix':numerical_substitution M piece ab ac(addM M(succM M count)(code_numeral M 1))
    (succM M(addM M count(zeroM M)))piece).
  { now rewrite!coding_add_zero_r in HMatrix|-*. }
  pose proof(source_upn_map_tail M count ib ic(code_numeral M 1)(zeroM M)ub uc(zeroM M)carrier HUp HHead)as HCarrier.
  rewrite coding_add_zero_r in HCarrier.
  assert(HCarrier':substitution_lookup M ub uc(addM M count(code_numeral M 1))
    (addM M count(zeroM M))count(addM M count carrier)).
  { now rewrite coding_add_zero_r. }
  destruct(source_ew_at_total M domain piece(addM M count carrier))as(ew'&HE').
  pose proof(source_ew_at_substitution M domain piece piece count(addM M count carrier)ew ew'
    ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M))ab ac
    (addM M(succM M count)(code_numeral M 1))HD HL HMatrix' HCarrier' HE HE')as HBody.
  exists ew'. split;[exact HE'|].
  exact(source_ballS_substitution M count(zeroM M)ew unary ib ic(code_numeral M 1)(zeroM M)
    carrier ew' out ub uc HHead HB HUp HBody HOut).
Qed.

Lemma source_piece_identity_prefix M count:exists b c,forall i,
  coding_lt M i count ->beta M b c i i.
Proof.
  set(rho:=fun _:nat=>zeroM M).
  assert(HT:forall i,coding_lt M i count ->exists v,holds M(v .:i .:rho)($0==$1)).
  { intros i _. exists i. apply substitution_holds_eq. reflexivity. }
  assert(HB:forall i v,coding_lt M i count ->holds M(v .:i .:rho)($0==$1) ->coding_lt M v(succM M count)).
  { intros i v HI HE. apply substitution_holds_eq in HE. change(v=i)in HE. subst v.
    apply coding_lt_succ_cases. now left. }
  assert(HU:forall i v w,coding_lt M i count ->holds M(v .:i .:rho)($0==$1) ->holds M(w .:i .:rho)($0==$1) ->v=w).
  { intros i v w _ HV HW. apply substitution_holds_eq in HV,HW. change(v=i)in HV. change(w=i)in HW. congruence. }
  destruct(beta_pack_function M rho($0==$1)count count HT HB HU)as(b&c&HBC).
  exists b,c. intros i HI. apply(proj2(HBC i i HI)),substitution_holds_eq. reflexivity.
Qed.

Theorem source_full_piece_witness_instance_elimination M domain count piece carrier out ew cb cc cn k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  context_bounded M cb cc cn k ->coding_lt M count(succM M k) ->coding_lt M carrier k ->
  source_piece_witness_instance M domain count piece carrier out ->source_ew_at M domain piece carrier ew ->
  source_full_prv M cb cc cn out ->
  (forall i member,coding_lt M i count ->sf_relation M SFMember i carrier member ->source_full_prv M cb cc cn member) ->
  source_full_prv M cb cc cn ew.
Proof.
  intros HD HP BC HC HY HW HE PW HM.
  destruct(source_piece_witness_instance_unroll M domain count piece carrier out HD HP HW)as(shifted&HShifted&HBall).
  pose proof(source_piece_witness_instance_bounded M domain count piece carrier out k HD HP HY HW)as BOut.
  pose proof(source_ballS_inverse_bound M count carrier shifted out k HBall BOut)as BShifted.
  destruct(source_piece_identity_prefix M count)as(b&c&HBC).
  assert(HFix:substitution_fixes_bound M b c count(zeroM M)count).
  { intros i HI. apply substitution_lookup_inside;[exact HI|exact(HBC i HI)]. }
  destruct(substitution_lift_total M b c count(zeroM M))as(ab&ac&an&HL).
  pose proof(substitution_lift_fixes_bound M b c count(zeroM M)ab ac an count HL HFix)as HFixA.
  pose proof(numerical_substitution_identity_on_bound M piece ab ac an(succM M(zeroM M))(succM M count)HP HFixA)as HMatrix.
  pose proof(source_ew_at_substitution M domain piece piece(addM M count carrier)carrier shifted ew b c count(zeroM M)ab ac an
    HD HL HMatrix(balls_prefix_tail M b c count carrier)HShifted HE)as HResult.
  assert(HMap:substitution_maps_bound M b c count(zeroM M)count k).
  { intros i v HI HV. pose proof(substitution_lookup_functional M b c count(zeroM M)i v i HV(HFix i HI))as E. subst v.
    exact(source_bound_lt_le M i count k HI HC). }
  assert(HMembers:balls_member_inputs M cb cc cn carrier b c count).
  { intros i v member HI HV HMember.
    pose proof(beta_unique M b c i v i HV(HBC i HI))as E. subst v. exact(HM i member HI HMember). }
  exact(source_full_ballS_elimination M count carrier shifted out ew b c cb cc cn k BC HY BShifted HMap HBall HResult PW HMembers).
Qed.
Print Assumptions source_piece_witness_instance_unroll.
Print Assumptions source_piece_identity_prefix.
Print Assumptions source_full_piece_witness_instance_elimination.
