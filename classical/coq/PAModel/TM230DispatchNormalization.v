(** Preserve the total header position while changing the read-prefix view.
    [base] is a fixed compiler padding bound; the excess is model-valued. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 TM230RuntimeWords TM230RuntimeTokens TM230DispatchWords TM230DispatchCode TM230DispatchCalibration
 TM230DispatchReadTape Program230PathCode.
From Stdlib Require Import Lists.List Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Section Normalize.
Variable M:Model.
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Add Ring dispatch_normalize_ring:(model_semiring M).
Lemma machine230_dispatch_header_position base n excess:
 (n<=base)%nat ->N n+(excess+N(base-n))=excess+N base.
Proof.
 intro H. replace(N n+(excess+N(base-n)))with(excess+(N n+N(base-n)))by ring.
 rewrite <-machine230_runtime_numeral_add.
 replace(n+(base-n))%nat with base by lia. reflexivity.
Qed.
Theorem machine230_dispatch_read_start base P Q n gap excess file s:
 (length Q<=base)%nat ->Q=firstn n(P++repeat false n)->
 Forall(eq false)(skipn n P)->N(length P)+gap=excess+N base ->
 machine230_dispatch_view M P gap 0 file s ->
 machine230_dispatch_view M Q excess(base-length Q)file s.
Proof.
 intros Hbound EQ Hclean Epos Hview.
 pose proof(machine230_dispatch_read_view M P Q n gap
  (excess+N(base-length Q))file s EQ Hclean
  ltac:(rewrite machine230_dispatch_header_position by exact Hbound;exact Epos)Hview)as Hnew.
 unfold machine230_dispatch_view in Hnew |-*. now rewrite coding_add_zero_r in Hnew.
Qed.
Theorem machine230_dispatch_code_read_start base P Q n pc depth gap excess file s:
 (length Q<=base)%nat ->Q=firstn n(P++repeat false n)->
 Forall(eq false)(skipn n P)->depth=N(length P)->pc=program230_path_value M P->
 depth+gap=excess+N base ->machine230_dispatch_code_view M pc depth gap file s ->
 machine230_dispatch_view M Q excess(base-length Q)file s.
Proof.
 intros Hbound EQ Hclean Ed Ep Epos Hview. subst depth pc.
 apply(machine230_dispatch_read_start base P Q n gap excess file s Hbound EQ Hclean Epos).
 apply machine230_dispatch_code_calibration. now rewrite coding_add_zero_r.
Qed.
Theorem machine230_dispatch_output_code base extra P excess file s:
 (length P<=base)%nat ->
 machine230_dispatch_view M P excess(base+extra-length P)file s ->
 machine230_dispatch_code_view M(program230_path_value M P)(N(length P))
  ((excess+N extra)+N(base-length P))file s /\
 N(length P)+((excess+N extra)+N(base-length P))=(excess+N extra)+N base.
Proof.
 intros HP Hview. split.
 -apply machine230_dispatch_code_calibration.
  apply(proj1(machine230_dispatch_rebase M P excess base extra(length P)file s HP));exact Hview.
 -apply machine230_dispatch_header_position;exact HP.
Qed.
End Normalize.
Print Assumptions machine230_dispatch_read_start.
Print Assumptions machine230_dispatch_code_read_start.
Print Assumptions machine230_dispatch_output_code.
