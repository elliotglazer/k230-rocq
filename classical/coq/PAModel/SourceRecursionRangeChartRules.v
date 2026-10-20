(** Both actual proof directions of the RR Replacement range chart. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint SourceDerivedRules
 SourceRecursionPrimitiveRelations SourceRecursionRangeFibre SourceRecursionRangeChart.
Unset Implicit Arguments.
Theorem source_full_rec_range_chart_out M cb cc cn phi o a N Y v chart member fibre:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_chart M phi o a N Y chart ->sf_relation M SFMember v Y member ->source_rec_range_fibre M phi o a N v fibre ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn member ->source_full_prv M cb cc cn fibre.
Proof.
 intros BP HC HM HF PC PM. destruct(source_rec_range_point_total M phi o a N Y v)as(point&HP).
 pose proof(source_full_rec_range_chart_use M cb cc cn phi o a N Y chart v point BP HC HP PC)as PP.
 destruct(source_rec_range_point_shell M phi o a N Y v point HP)as(member'&fibre'&forward&backward&HM'&HF'&HForward&HBackward&HAnd).
 pose proof(sf_relation_functional M SFMember v Y member' member HM' HM)as E. subst member'.
 pose proof(source_rec_range_fibre_functional M phi o a N v fibre' fibre HF' HF)as E. subst fibre'.
 pose proof(proj1(source_full_piece_conjunction_components M cb cc cn forward backward point HAnd PP))as PForward.
 exact(source_full_modus_ponens M cb cc cn member fibre forward HForward PForward PM).
Qed.
Theorem source_full_rec_range_chart_in M cb cc cn phi o a N Y v chart member fibre:
 source_bounded M phi(code_numeral M 2) ->source_rec_range_chart M phi o a N Y chart ->sf_relation M SFMember v Y member ->source_rec_range_fibre M phi o a N v fibre ->
 source_full_prv M cb cc cn chart ->source_full_prv M cb cc cn fibre ->source_full_prv M cb cc cn member.
Proof.
 intros BP HC HM HF PC PF. destruct(source_rec_range_point_total M phi o a N Y v)as(point&HP).
 pose proof(source_full_rec_range_chart_use M cb cc cn phi o a N Y chart v point BP HC HP PC)as PP.
 destruct(source_rec_range_point_shell M phi o a N Y v point HP)as(member'&fibre'&forward&backward&HM'&HF'&HForward&HBackward&HAnd).
 pose proof(sf_relation_functional M SFMember v Y member' member HM' HM)as E. subst member'.
 pose proof(source_rec_range_fibre_functional M phi o a N v fibre' fibre HF' HF)as E. subst fibre'.
 pose proof(proj2(source_full_piece_conjunction_components M cb cc cn forward backward point HAnd PP))as PBackward.
 exact(source_full_modus_ponens M cb cc cn fibre member backward HBackward PBackward PF).
Qed.
Print Assumptions source_full_rec_range_chart_out.
Print Assumptions source_full_rec_range_chart_in.
