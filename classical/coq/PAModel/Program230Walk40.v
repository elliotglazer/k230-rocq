(** Fixed-depth control selection for arbitrary PA-model PCs.
    The input PC need not be the code of an external finite path. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 Program230PathCode Program230PathPop Program230Read Program230Walk Program230Height.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Theorem program230_numeric_walk_depth_40 M code e Q rest :
 program230_walk M p230 code e Q rest ->(length Q<=40)%nat.
Proof.
 intros [HR [HF HL]].
 pose proof (walk_leaf p230 p230_wf Q e Q HF HL (fun i=>eq_refl)) as HW.
 exact (program230_walk_depth_40 (nnodes p230+1) Q e (length Q) HW).
Qed.

Theorem program230_numeric_walk_40_total M code : code<>zeroM M ->
 exists e Q rest,program230_walk M p230 code e Q rest /\(length Q<=40)%nat.
Proof.
 intro Hnz.
 destruct (program230_read_total M 40 code Hnz) as [bits [rest [Hlen [HR Hrest]]]].
 destruct (program230_walk_40_total bits) as [e [d HW]].
 pose proof (program230_walk_depth_40 40 bits e d HW) as HD.
 assert (HD' : (d<=length bits)%nat) by lia.
 destruct (program230_read_firstn M code bits rest d HR) as [middle HP].
 exists e,(program230_take_zeros d bits),middle;split.
 -unfold program230_walk;split.
  +rewrite (program230_take_zeros_firstn d bits HD');exact HP.
  +split.
   *rewrite program230_take_zeros_source_prefix,pad_bits.
    pose proof (walk_fol p230 40 (root p230) bits 0 e d HW) as HF.
    now rewrite Nat.sub_0_r in HF.
   *exact (proj2 (walk_gt p230 40 (root p230) bits 0 e d HW)).
 -rewrite program230_take_zeros_length;exact HD.
Qed.

Theorem program230_numeric_walk_40_source_exact M P e Q rest :
 program230_walk M p230 (program230_path_value M P) e Q rest ->
 walk p230 40 (root p230) P 0=Some(e,length Q) /\
 (length Q<=40)%nat /\
 Q=firstn (length Q) (P++repeat false (length Q)) /\
 rest=program230_path_value M (skipn (length Q) P).
Proof.
 intro HW. pose proof (program230_numeric_walk_depth_40 M _ _ _ _ HW) as HD.
 destruct (program230_walk_source_exact M p230 P e Q rest p230_wf HW)
  as [HS [HQ HR]].
 split;[apply (proj1 (program230_walk_40_exact P e (length Q)));exact HS|].
 split;[exact HD|split;assumption].
Qed.

Theorem program230_numeric_walk_40_source M P e d :
 walk p230 40 (root p230) P 0=Some(e,d) ->
 program230_walk M p230 (program230_path_value M P) e
  (program230_take_zeros d P) (program230_path_value M (skipn d P)).
Proof. apply program230_walk_source. Qed.

Print Assumptions program230_numeric_walk_depth_40.
Print Assumptions program230_numeric_walk_40_total.
Print Assumptions program230_numeric_walk_40_source_exact.
Print Assumptions program230_numeric_walk_40_source.
