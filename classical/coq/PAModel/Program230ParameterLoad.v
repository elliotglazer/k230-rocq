(** Actual parameter-1 loading: copy register4 into top/scratch, then restore it. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions Program230PathCode
 Program230Configurations Program230Histories Program230TransferProgram Program230TransferLoop
 Program230Copy2Program Program230Copy2Loop Program230SemanticHistories Program230CopyEntry Program230TransferEntry
 Program230PairConstructorIteration.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_parameter_shape P r:=
 (exists n m k,program230_copy2_occurrence p230(P++[false])r 1 6 n m k) /\
 (exists n m,program230_transfer_occurrence p230(P++[true])6 r n m).
Theorem program230_parameter_history M P r start:
 (r<9)%nat->r<>1->r<>6->
 program230_parameter_shape P r->program230_pc start=program230_path_value M P->
 program230_register start 1=zeroM M->program230_register start 6=zeroM M->
 exists b c time last,program230_program_history M p230 b c time start /\
 program230_state_at M b c time last /\coding_lt M(zeroM M)time /\
 program230_pc last=program230_path_value M(inc_path(P++[true])) /\
 program230_register last 1=program230_register start r /\program230_register last 6=zeroM M /\
 (forall i,(i<9)%nat->i<>1->i<>6->program230_register last i=program230_register start i).
Proof.
 intros Hr Hr1 Hr6 [[n[m[k Hcopy]]][u[v Htransfer]]]HP H1 H6.
 set(count:=program230_register start r).
 destruct(p230_copy2_padded_entry M(P++[false])P r 1 6 n m k start count
 Hr ltac:(lia)ltac:(lia)Hr1 Hr6 ltac:(lia)Hcopy HP(ipeq_sym _ _(ipeq_app_false P))eq_refl)
 as[a[b[mid[HA[HTA[Hmidpc[H4[HM1[HM6 HO]]]]]]]]].
 rewrite inc_path_app_false in Hmidpc.
 assert(Hcount:program230_register mid 6=count)by(rewrite HM6,H6,coding_add_zero;reflexivity).
 destruct(p230_transfer_padded_entry M(P++[true])(P++[true])6 r u v mid count
 ltac:(lia)Hr ltac:(congruence)Htransfer Hmidpc(ipeq_refl _)Hcount)
 as[c[d[last[HC[HTC[Hlastpc[HL6[HL4 HF]]]]]]]].
 destruct(p230_program_history_join M a b(program230_copy2_time M count)c d(program230_transfer_time M count)
 start mid HA HTA HC)as[e[f[HR[HH HJ]]]].
 exists e,f,(addM M(program230_copy2_time M count)(program230_transfer_time M count)),last.
 split;[exact HR|]. split.
 -exact(proj1(HJ(program230_transfer_time M count)_(coding_lt_succ M(program230_transfer_time M count)))HTC).
 -split;[apply program230_duration_add;apply program230_transfer_time_positive|].
  split;[exact Hlastpc|]. split.
  +rewrite(HF 1 ltac:(lia)ltac:(lia)ltac:(congruence)),HM1,H1,coding_add_zero;reflexivity.
  +split;[exact HL6|]. intros i Hi Hi1 Hi6.
   destruct(Nat.eq_dec i r)as[->|Hi4].
   *rewrite HL4,H4,coding_add_zero;reflexivity.
   *rewrite(HF i Hi Hi6 Hi4),(HO i Hi Hi4 Hi1 Hi6);reflexivity.
Qed.
Print Assumptions program230_parameter_history.
