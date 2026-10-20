(** Uniform TV closes the actual internally many bounded parameter
    quantifiers when its witness and containment inputs have been proved. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking CodeExpressions SetFormulaCodes
  SourceBounded SourceBoundMonotone NumericalContexts NumericalSourceFull SourceTraceBounds
  SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
  SourceIffGraphs SourceBallS SourceBallSIntroduction SourceTarskiVaughtInputs SourceTarskiVaughtInvariant
  SourceTarskiVaughtUniform SourceTarskiVaughtShiftedProofs.
Unset Implicit Arguments.

Theorem source_full_tv_ballS M domain phi count Y left right equiv block b c n k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  context_bounded M b c n k ->coding_lt M Y k ->
  source_relativization M domain phi left ->source_set_relativization M(addM M count Y)phi right ->
  source_iff_graph M left right equiv ->source_ballS M count Y equiv block ->
  source_tv_witnesses M domain phi count Y b c n ->source_tv_containment M domain Y b c n ->
  source_full_prv M b c n block.
Proof.
  intros HD HP BC HY HL HR HE HB HW HC.
  pose proof(source_bounded_monotone M phi count(addM M count k)HP(coding_le_add M count k))as BP.
  pose proof(source_relativization_preserves_bound M phi domain(addM M count k)left HD BP HL)as BL.
  pose proof(source_set_relativization_preserves_bound M phi(addM M count Y)(addM M count k)right
    (coding_lt_add_left M count Y k HY)BP HR)as BR.
  pose proof(source_iff_bounded M left right equiv(addM M count k)BL BR HE)as BE.
  apply(source_full_ballS_introduction M count Y equiv block b c n k BC HY BE HB).
  intros ub uc un width BT HProofs HMembers.
  set(wide:=addM M(addM M count k)width).
  assert(BWide:context_bounded M ub uc un wide).
  { apply(context_bounded_monotone M ub uc un width wide BT).
    unfold wide. rewrite Arithmetic.add_comm. apply coding_le_add. }
  assert(CountWide:coding_lt M count(succM M wide)).
  { unfold wide. rewrite <-Arithmetic.add_assoc. apply coding_le_add. }
  assert(YWide:coding_lt M(addM M count Y)wide).
  { unfold wide.
    apply(source_bound_lt_le M(addM M count Y)(addM M count k)(addM M(addM M count k)width)).
    - exact(coding_lt_add_left M count Y k HY).
    - apply coding_le_add. }
  assert(HWitness:source_tv_witnesses M domain phi count(addM M count Y)ub uc un).
  { rewrite(Arithmetic.add_comm M count Y).
    exact(source_tv_witnesses_shifted_proofs M domain phi count Y b c n count ub uc un width HD HP BT HProofs HW). }
  assert(HContain:source_tv_containment M domain(addM M count Y)ub uc un).
  { rewrite(Arithmetic.add_comm M count Y).
    exact(source_tv_containment_shifted_proofs M domain Y b c n count ub uc un width HD BT HProofs HC). }
  exact(source_full_tarski_vaught M phi domain count(addM M count Y)left right equiv ub uc un wide
    HD HP BWide CountWide YWide HL HR HE HMembers HWitness HContain).
Qed.

Print Assumptions source_full_tv_ballS.
