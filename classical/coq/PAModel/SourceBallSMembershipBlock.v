(** Consume the actual internally finite membership conjunction used by
    L_common, rather than a family of unproved membership certificates. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  NumericalContexts NumericalSourceFull NumericalSubstitutionMaps NumericalSubstitution SourceBounded SourceSubstitutionBounds
  SourceBoundedMapComposition SourceMembershipBlocks SourceMembershipBlockProofs SourceBallS SourceBallSElimination.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition balls_offset_assignment M start count b c:=forall i v,coding_lt M i count ->
  (beta M b c i v<->v = addM M i start).
Theorem balls_offset_assignment_total M start count:exists b c,balls_offset_assignment M start count b c.
Proof.
  set(rho:=start .:fun _=>zeroM M). set(F:=($0==$1⊕$2):form).
  assert(HT:forall i,coding_lt M i count->exists v,holds M(v .:i .:rho)F).
  { intros i _. exists(addM M i start). reflexivity. }
  assert(HU:forall i v w,coding_lt M i count->holds M(v .:i .:rho)F->holds M(w .:i .:rho)F->v=w).
  { intros i v w _ HV HW. change(v = addM M i start)in HV. change(w = addM M i start)in HW. congruence. }
  destruct(beta_pack_total_function M rho F count HT HU)as(b&c&HBC).
  exists b,c. intros i v HI. exact(HBC i v HI).
Qed.
Theorem source_full_ballS_membership_block M count y body out result start block b c gb gc gn k:
  context_bounded M gb gc gn k ->coding_lt M y k ->source_bounded M body(addM M count k) ->
  (forall i,coding_lt M i count->coding_lt M(addM M i start)k) ->
  balls_offset_assignment M start count b c ->source_ballS M count y body out ->
  source_membership_block M start y count block ->numerical_substitution M body b c count(zeroM M)result ->
  source_full_prv M gb gc gn out ->source_full_prv M gb gc gn block ->source_full_prv M gb gc gn result.
Proof.
  intros HC HY HB HNames HAssign HBall HBlock HSub PBall PBlock.
  assert(HMap:substitution_maps_bound M b c count(zeroM M)count k).
  { intros i v HI HV. apply(proj1(substitution_lookup_inside M b c count(zeroM M)i v HI))in HV.
    pose proof(proj1(HAssign i v HI)HV)as E. subst v. exact(HNames i HI). }
  apply(source_full_ballS_elimination M count y body out result b c gb gc gn k
    HC HY HB HMap HBall HSub PBall).
  intros i t member HI HT HM. pose proof(proj1(HAssign i t HI)HT)as E. subst t.
  exact(source_full_membership_block_project M start y count block gb gc gn k i member
    HNames HY HBlock HC PBlock HI HM).
Qed.
Theorem source_full_ballS_membership_block_total M count y body out start block gb gc gn k:
  context_bounded M gb gc gn k ->coding_lt M y k ->source_bounded M body(addM M count k) ->
  (forall i,coding_lt M i count->coding_lt M(addM M i start)k) ->
  source_ballS M count y body out ->source_membership_block M start y count block ->
  source_full_prv M gb gc gn out ->source_full_prv M gb gc gn block ->
  exists b c result,balls_offset_assignment M start count b c /\
    numerical_substitution M body b c count(zeroM M)result /\source_full_prv M gb gc gn result.
Proof.
  intros HC HY HB HNames HBall HBlock PBall PBlock.
  destruct(balls_offset_assignment_total M start count)as(b&c&HAssign).
  destruct(numerical_substitution_total M body b c count(zeroM M))as(result&HSub).
  exists b,c,result. split;[exact HAssign|]. split;[exact HSub|].
  exact(source_full_ballS_membership_block M count y body out result start block b c gb gc gn k
    HC HY HB HNames HAssign HBall HBlock HSub PBall PBlock).
Qed.
Print Assumptions balls_offset_assignment_total.
Print Assumptions source_full_ballS_membership_block.
Print Assumptions source_full_ballS_membership_block_total.
