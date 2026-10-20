(** The exact364 public AX rows compose their literal per-operation histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding NumericalProofs CodeExpressions
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230AXSymbolic Program230AXSymbolicGraphs Program230AXNativeSymbolic Program230AXSymbolicTrace
 Program230AXPathSchedule Program230AXPrimitiveSchedule Program230AXTypedNormalization Program230AXTraceLinks
 Program230AXRuntimeInterface Program230AXHistoryFold.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Fixpoint p230_ax_fold_connectorsb(rows:list p230_ax_fold_row)(exit:list bool):bool:=
 match rows with []=>true|row::tail=>ax_ipeqb(ax_primitive_exit(fst row))(p230_ax_fold_entry tail exit) &&p230_ax_fold_connectorsb tail exit end.
Lemma p230_ax_fold_connectorsb_sound rows exit:
 p230_ax_fold_connectorsb rows exit=true->p230_ax_fold_connectors rows exit.
Proof.
 induction rows as[|row tail IH];cbn[p230_ax_fold_connectorsb p230_ax_fold_connectors];[intros _;exact I|].
 intro H;apply Bool.andb_true_iff in H;destruct H as[Hhead Htail];split;[apply ax_ipeqb_sound;exact Hhead|exact(IH Htail)].
Qed.
Theorem p230_ax_public_fold_connectors:p230_ax_fold_connectors p230_ax_typed_rows p230_ax_schedule_gate.
Proof. apply p230_ax_fold_connectorsb_sound;vm_compute;reflexivity. Qed.
Lemma p230_ax_fold_links_of_trace before rows after:
 p230_ax_trace_links before(map snd rows)after->p230_ax_fold_links before rows after.
Proof.
 induction rows as[|row tail IH]in before|-*;[exact(fun H=>H)|].
 destruct row as[item[[op old]next]];cbn[p230_ax_trace_links p230_ax_fold_links p230_ax_fold_before p230_ax_fold_after];
 intros[HE HL];split;[exact HE|exact(IH next HL)].
Qed.
Theorem p230_ax_public_fold_links:
 p230_ax_fold_links p230_ax_symbolic_initial p230_ax_typed_rows p230_ax_symbolic_final.
Proof.
 apply p230_ax_fold_links_of_trace;rewrite p230_ax_typed_rows_states;exact p230_ax_native_rows_linked.
Qed.
Definition p230_ax_public_row_implementations M env:Prop:=
 forall item op before after,In(item,(op,before,after))p230_ax_typed_rows->forall start,
 program230_pc start=program230_path_value M(fst(fst item))->
 p230_ax_register_graph M env before start->
 p230_ax_runtime_result M env after start(ax_primitive_exit item).
Local Opaque p230_ax_typed_rows p230_ax_primitive_schedule.
Theorem p230_ax_public_history_fold M env start:
 p230_ax_public_row_implementations M env->
 program230_pc start=program230_path_value M p230_ax_schedule_root->
 p230_ax_register_graph M env p230_ax_symbolic_initial start->
 exists b c time last finalpath,program230_history M p230_instruction_formula b c time start /\
 program230_state_at M b c time last /\coding_lt M(zeroM M)time /\
 program230_pc last=program230_path_value M finalpath /\ipeq finalpath p230_ax_schedule_gate /\
 p230_ax_register_graph M env p230_ax_symbolic_final last.
Proof.
 intros Himpl Hpc HG.
 assert(Hrows:Forall(p230_ax_runtime_row M env)p230_ax_typed_rows).
 {apply Forall_forall;intros[item[[op before]after]]Hin.
  intros actual HP HA.
  destruct(Himpl item op before after Hin actual HP HA)as[b[c[time[last[HR[HT[HN[HL HF]]]]]]]].
  apply(proj1(p230_instruction_history_correct M b c time actual))in HR.
  exists b,c,time,last;exact(conj HR(conj HT(conj HN(conj HL HF)))). }
 assert(Hentry:ipeq p230_ax_schedule_root(p230_ax_fold_entry p230_ax_typed_rows p230_ax_schedule_gate)).
 {apply ax_ipeqb_sound;vm_compute;reflexivity. }
 destruct(p230_ax_finite_history_fold M env p230_ax_typed_rows Hrows p230_ax_symbolic_initial p230_ax_symbolic_final
 p230_ax_schedule_gate start p230_ax_schedule_root p230_ax_public_fold_links p230_ax_public_fold_connectors Hpc Hentry HG)
 as[b[c[time[last[finalpath[HR[HT[HP[HE[HF HN]]]]]]]]]].
 apply(proj2(p230_instruction_history_correct M b c time start))in HR.
 exists b,c,time,last,finalpath;split;[exact HR|]. split;[exact HT|].
 split.
 -apply HN;intro E;pose proof(f_equal(@length _)p230_ax_typed_rows_positions)as Hlength.
  rewrite E in Hlength;change(0=length p230_ax_primitive_schedule)in Hlength;rewrite p230_ax_primitive_count in Hlength;discriminate.
 - split;[exact HP|]. split;[exact HE|exact HF].
Qed.
Print Assumptions p230_ax_public_fold_connectors.
Print Assumptions p230_ax_public_fold_links.
Print Assumptions p230_ax_public_history_fold.
