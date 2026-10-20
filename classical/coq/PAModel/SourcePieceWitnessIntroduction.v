(** Close an actual pointwise Ew proof family into the exact unary
    witness-closure instance consumed by uniform Tarski-Vaught. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
  SourcePieceWitnessInstance SourcePieceWitnessUnroll SourceEwAtSyntax SourceEwMonotone
  SourceBallSIntroduction SourceBallSInverseBounds.
Unset Implicit Arguments.
Theorem source_full_piece_witness_instance_introduction M domain count piece carrier out ew cb cc cn k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M piece(succM M count) ->
  context_bounded M cb cc cn k ->coding_lt M carrier k ->
  source_piece_witness_instance M domain count piece carrier out ->
  source_ew_at M domain piece(addM M count carrier)ew ->
  source_balls_open_proof M cb cc cn count carrier ew ->source_full_prv M cb cc cn out.
Proof.
  intros HD HP BC HY HW HE HOpen.
  destruct(source_piece_witness_instance_unroll M domain count piece carrier out HD HP HW)as(body&HB&HBall).
  pose proof(source_ew_at_functional M domain piece(addM M count carrier)body ew HB HE)as E. subst body.
  pose proof(source_piece_witness_instance_bounded M domain count piece carrier out k HD HP HY HW)as BOut.
  exact(source_full_ballS_introduction M count carrier ew out cb cc cn k BC HY
    (source_ballS_inverse_bound M count carrier ew out k HBall BOut)HBall HOpen).
Qed.
Print Assumptions source_full_piece_witness_instance_introduction.
