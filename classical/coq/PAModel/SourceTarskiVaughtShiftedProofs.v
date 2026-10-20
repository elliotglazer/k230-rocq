(** Transport actual witness/containment proofs below an arbitrary internal
    number of binders, using actual shifted proofs of the old hypotheses. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalContextRenaming NumericalRenamingMaps NumericalRenaming NumericalSourceFull
  SourceProofRenaming SourceHypothesisTransport SourceQuantifierPieces SourcePCSPieces SourcePieceWitnessInstance
  SourceTarskiVaughtInputs SourceBallSIntroduction SourceRelativizationRules SourceSetRelativizationRules
  SourceSetRelativizationRenaming SourceRenamingIdentity.
Unset Implicit Arguments.

Theorem source_full_prv_shifted_hypotheses M b c n f delta g ub uc un k:
  context_bounded M ub uc un k ->source_full_prv M b c n f ->
  numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)delta g ->
  source_shifted_context_proofs M b c n delta ub uc un ->source_full_prv M ub uc un g.
Proof.
  intros BC PF HR HP.
  destruct(context_renaming_total M b c n(zeroM M)(zeroM M)(zeroM M)delta)as(sb&sc&HC).
  pose proof(source_full_prv_renaming M b c n f(zeroM M)(zeroM M)(zeroM M)delta sb sc g PF HC HR)as PG.
  apply(source_full_prv_replace_hypotheses M ub uc un(ex_intro _ k BC)n sb sc g PG).
  intros h HH.
  destruct(proj1(context_renaming_member_iff M b c n(zeroM M)(zeroM M)(zeroM M)delta sb sc h HC)HH)
    as(old&HO&HS).
  exact(HP old h HO HS).
Qed.

Theorem source_tv_witnesses_shifted_proofs M domain phi count Y b c n delta ub uc un k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  context_bounded M ub uc un k ->source_shifted_context_proofs M b c n delta ub uc un ->
  source_tv_witnesses M domain phi count Y b c n ->
  source_tv_witnesses M domain phi count(addM M Y delta)ub uc un.
Proof.
  intros HD HP BC HS HW pc body piece out HBody HSign HOut.
  pose proof(source_quantifier_body_bounded M phi count pc body HBody HP)as BB.
  pose proof(source_pcs_sign_bounded M domain body piece(succM M pc)HD BB HSign)as BP.
  destruct(source_piece_witness_instance_total M domain pc piece Y)as(old&HOld).
  apply(source_full_prv_shifted_hypotheses M b c n old delta out ub uc un k BC
    (HW pc body piece old HBody HSign HOld));[|exact HS].
  apply(source_piece_witness_instance_renaming_graph M domain pc piece Y old
    (zeroM M)(zeroM M)(zeroM M)delta(addM M Y delta)out HD BP HOld);[|exact HOut].
  apply(proj2(source_empty_shift_lookup M delta Y(addM M Y delta))). reflexivity.
Qed.

Theorem source_tv_containment_shifted_proofs M domain Y b c n delta ub uc un k:
  source_bounded M domain(code_numeral M 1) ->context_bounded M ub uc un k ->
  source_shifted_context_proofs M b c n delta ub uc un ->
  source_tv_containment M domain Y b c n ->
  source_tv_containment M domain(addM M Y delta)ub uc un.
Proof.
  intros HD BC HS(old&HOld&POld).
  destruct(ssr_quantifier_total M true(addM M Y delta)domain)as(out&HOut).
  destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)delta)as(rb&rc&rn&HL).
  pose proof(numerical_renaming_lift_fixes_domain M domain(zeroM M)(zeroM M)(zeroM M)delta rb rc rn HD HL)as HRDomain.
  assert(HY:renaming_lookup M(zeroM M)(zeroM M)(zeroM M)delta Y(addM M Y delta)).
  { apply(proj2(source_empty_shift_lookup M delta Y(addM M Y delta))). reflexivity. }
  pose proof(ssr_quantifier_renaming M true Y(addM M Y delta)domain old
    (zeroM M)(zeroM M)(zeroM M)delta rb rc rn domain out HY HL HOld HRDomain HOut)as HR.
  exists out. split;[exact HOut|].
  exact(source_full_prv_shifted_hypotheses M b c n old delta out ub uc un k BC POld HR HS).
Qed.

Print Assumptions source_full_prv_shifted_hypotheses.
Print Assumptions source_tv_witnesses_shifted_proofs.
Print Assumptions source_tv_containment_shifted_proofs.
