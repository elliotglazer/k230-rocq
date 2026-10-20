(** Turn an actual ordinary PH point theorem into an actual witness-closure
    telescope, discharging every parameter-membership binder by real BallS rules. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking CodeExpressions
  SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull NumericalRenaming SourceRenamingIdentity
  SourceTraceBounds SourceZFRProvability SourceFiniteTelescope SourcePieceWitnessInstance SourcePieceWitnessIntroduction
  SourceBallSIntroduction SourceTarskiVaughtShiftedProofs SourceEwAtSyntax SourceEwMonotone
  SourceMembershipBlocks SourceMembershipBlockProofs SourceHypothesisTransport.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfr_piece_witness_from_point M domain params piece Y wh ew block A AS pointLaw law k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M params) ->coding_lt M Y k ->
  source_piece_witness_instance M domain params piece Y wh ->source_ew_at M domain piece(addM M params Y)ew ->
  source_membership_block M(zeroM M)(addM M params Y)params block ->
  Forall2(fun a shifted=>numerical_renaming M a(zeroM M)(zeroM M)(zeroM M)params shifted)A AS ->
  (forall a,In a A ->source_bounded M a k) ->
  source_finite_telescope M(AS++[block])ew pointLaw ->source_finite_telescope M A wh law ->
  source_zfr_provable M pointLaw ->source_zfr_provable M law.
Proof.
  intros HD HP HY HWh HE HBlock HShift BA HPoint HLaw(ab&ac&an&HClosed&PPoint).
  pose proof(source_zfr_context_closed M ab ac an HClosed)as BClosed.
  pose proof(context_bounded_monotone M ab ac an(zeroM M)k BClosed(coding_zero_lt_succ M k))as BBase.
  pose proof(source_piece_witness_instance_bounded M domain params piece Y wh k HD HP HY HWh)as BWh.
  exists ab,ac,an. split;[exact HClosed|].
  apply(source_full_finite_telescope M A wh law k BA BWh HLaw ab ac an BBase).
  intros b c n BC Included Premises.
  apply(source_full_piece_witness_instance_introduction M domain params piece Y wh ew b c n k
    HD HP BC HY HWh HE).
  intros ub uc un width BT HProofs HMembers.
  set(wide:=addM M(addM M params k)width).
  assert(BWide:context_bounded M ub uc un wide).
  { apply(context_bounded_monotone M ub uc un width wide BT).
    unfold wide. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert(ParamsWide:coding_lt M params(succM M wide)).
  { unfold wide. rewrite <-Arithmetic.add_assoc. apply coding_le_add. }
  assert(YWide:coding_lt M(addM M params Y)wide).
  { unfold wide. apply(source_bound_lt_le M(addM M params Y)(addM M params k)(addM M(addM M params k)width)).
    - exact(coding_lt_add_left M params Y k HY).
    - apply coding_le_add. }
  assert(PPointTarget:source_full_prv M ub uc un pointLaw).
  { apply(source_full_prv_replace_hypotheses M ub uc un(ex_intro _ wide BWide)an ab ac pointLaw PPoint).
    intros ax HAx. apply(HProofs ax ax(Included ax HAx)).
    apply(numerical_renaming_identity_on_bound M ax(zeroM M)(zeroM M)(zeroM M)params(zeroM M)(BClosed ax HAx)).
    intros i HI. exfalso. exact(coding_not_lt_zero M i HI). }
  assert(PShifted:forall a,In a AS ->source_full_prv M ub uc un a).
  { clear -HShift BT HProofs Premises. revert Premises.
    induction HShift as[|a shifted A AS HR HRest IH];intros Premises f HF;[contradiction|].
    destruct HF as[EF|HF].
    - subst f. exact(source_full_prv_shifted_hypotheses M b c n a params shifted ub uc un width
        BT(Premises a(or_introl eq_refl))HR HProofs).
    - exact(IH(fun a' HA=>Premises a'(or_intror HA))f HF). }
  assert(PBlock:source_full_prv M ub uc un block).
  { apply(source_full_membership_block_intro M(zeroM M)(addM M params Y)params block ub uc un wide).
    - intros i HI. rewrite coding_add_zero_r. exact(source_bound_lt_le M i params wide HI ParamsWide).
    - exact YWide.
    - exact HBlock.
    - exact BWide.
    - intros i member HI HM. rewrite coding_add_zero_r in HM. exact(HMembers i member HI HM). }
  apply(source_full_finite_telescope_apply M(AS++[block])ew pointLaw HPoint ub uc un PPointTarget).
  intros a HA. apply in_app_or in HA. destruct HA as[HA|[EA|[]]];[exact(PShifted a HA)|now subst a].
Qed.

Print Assumptions source_zfr_piece_witness_from_point.
