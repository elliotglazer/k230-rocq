(** Actual positive machine execution preserves the arithmetic dispatcher
    graph for every checked program edge and every model-valued register file. *)
From PAModel Require Import Model Arithmetic CodeExpressions
 TM230BinaryStep TM230MacroProgress TM230RuntimeWords TM230RuntimeSites TM230RuntimeBox
 TM230DispatchWords TM230DispatchCode TM230DispatchNormalization TM230LogicalSites
 TM230PhysicalRegisters Program230PathCode Program230Edges.
From K230 Require RM Interpreter230Check Interpreter230Sites.
From Stdlib Require Import Lists.List Lia Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Lemma machine230_inc_length_rev P:length(K230.RM.inc_rev P)=length P.
Proof. induction P as[|b P IH];[reflexivity|]. destruct b;cbn[K230.RM.inc_rev];cbn;auto. Qed.
Lemma machine230_inc_path_length P:length(K230.RM.inc_path P)=length P.
Proof. unfold K230.RM.inc_path;rewrite length_rev,machine230_inc_length_rev,length_rev;reflexivity. Qed.
Lemma machine230_strip_length_rev P b k:(length(K230.RM.strip_rev b k P)<=length P)%nat.
Proof.
 revert b k;induction P as[|x P IH];intros b k;destruct k as[|k];cbn[K230.RM.strip_rev];cbn;try lia.
 destruct(Bool.eqb x b);cbn;[specialize(IH b k)|specialize(IH b(S k))];lia.
Qed.
Lemma machine230_edge_path_length P e z:(length(machine230_edge_path P e z)<=length P)%nat.
Proof.
 destruct e;cbn[machine230_edge_path];try lia.
 -rewrite machine230_inc_path_length;lia.
 -destruct z;[unfold K230.RM.brk|];rewrite machine230_inc_path_length;try lia.
  unfold K230.RM.strip_path;rewrite length_rev;pose proof(machine230_strip_length_rev(rev P)false 1);rewrite length_rev in H;exact H.
 -unfold K230.RM.brk,K230.RM.strip_path;rewrite machine230_inc_path_length,length_rev.
  pose proof(machine230_strip_length_rev(rev P)false k);rewrite length_rev in H;exact H.
 -unfold K230.RM.cont,K230.RM.strip_path;rewrite length_rev.
  pose proof(machine230_strip_length_rev(rev P)true k);rewrite length_rev in H;exact H.
Qed.
Definition machine230_edge_extra Q e z:=((if machine230_edge_overflow Q e z then 1 else 0)+machine230_edge_boundary e z)%nat.
Theorem machine230_dispatch_code_program_edge M P Q read e R T pc pc' E depth gap excess input s:
 (length Q<=40)%nat ->K230.Interpreter230Check.check_edge Q e=true ->
 program230_edge_step M Q e R T pc' ->
 Q=firstn read(P++repeat false read)->Forall(eq false)(skipn read P)->
 depth=code_numeral M(length P)->pc=program230_path_value M P ->
 addM M depth gap=addM M excess(code_numeral M Sites230.D0) ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)input ->
 machine230_dispatch_code_view M pc depth gap input s ->
 exists z output t,
 pc'=program230_path_value M(machine230_edge_path Q e z) /\
 (length(machine230_edge_path Q e z)<=40)%nat /\
 machine230_runtime_box M(machine230_physical_values M T)(machine230_edge_spares M e E)(Runtime230.BPlain Runtime230.FNone)output /\
 machine230_dispatch_code_view M pc'(code_numeral M(length(machine230_edge_path Q e z)))
  (addM M(addM M excess(code_numeral M(machine230_edge_extra Q e z)))
  (code_numeral M(Sites230.D0-length(machine230_edge_path Q e z))))output t /\
 machine230_progresses M s t.
Proof.
 intros HQ HC HE EQ Hclean Ed Ep Hpos HX HS.
 assert(HQB:(length Q<=Sites230.D0)%nat)by(unfold Sites230.D0;lia).
 pose proof(machine230_dispatch_code_read_start M Sites230.D0 P Q read pc depth gap excess input s
  HQB EQ Hclean Ed Ep Hpos HS)as Hstart.
 destruct(machine230_checked_program_edge M Q e R T pc' E excess input s HC HE HX Hstart)
  as[z[output[t[Hpc[HBox[Htarget Hpath]]]]]].
 assert(HP:(length(machine230_edge_path Q e z)<=Sites230.D0)%nat).
 {pose proof(machine230_edge_path_length Q e z);lia. }
 assert(HT:machine230_dispatch_view M(machine230_edge_path Q e z)excess
  (Sites230.D0+machine230_edge_extra Q e z-length(machine230_edge_path Q e z))output t).
 {replace(Sites230.D0+machine230_edge_extra Q e z-length(machine230_edge_path Q e z))%nat with
  (Sites230.D0+(if machine230_edge_overflow Q e z then 1 else 0)+machine230_edge_boundary e z-length(machine230_edge_path Q e z))%nat
  by(unfold machine230_edge_extra;lia). exact Htarget. }
 destruct(machine230_dispatch_output_code M Sites230.D0(machine230_edge_extra Q e z)
  (machine230_edge_path Q e z)excess output t HP HT)as[Hcode Htotal].
 exists z,output,t;split;[exact Hpc|]. split;[pose proof(machine230_edge_path_length Q e z);lia|].
 split;[exact HBox|]. split;[now rewrite Hpc|exact Hpath].
Qed.
Print Assumptions machine230_edge_path_length.
Print Assumptions machine230_dispatch_code_program_edge.
