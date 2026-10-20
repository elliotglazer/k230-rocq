(** Actual history composition over an externally fixed finite typed instruction trace.
 The per-row implementation is explicit here and must be discharged by literal site proofs. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Configurations Program230Histories Program230InstructionFormula
 Program230RootHistory Program230TransferProgram Program230TransferEntry Program230SemanticHistories
 Program230UnpairRestore Program230MPTransport Program230AXSymbolicGraphs Program230AXNativeSymbolic
 Program230AXSymbolicTrace Program230AXPrimitiveSchedule Program230AXTypedNormalization.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_fold_row:Type:=((list bool*edge)*(ax_primitive_op*nat))*p230_ax_native_row.
Definition p230_ax_fold_path(row:p230_ax_fold_row):list bool:=fst(fst(fst row)).
Definition p230_ax_fold_before(row:p230_ax_fold_row):program230_configuration code_expr:=snd(fst(snd row)).
Definition p230_ax_fold_after(row:p230_ax_fold_row):program230_configuration code_expr:=snd(snd row).
Definition p230_ax_runtime_row M env(row:p230_ax_fold_row):Prop:=forall start,
 program230_pc start=program230_path_value M(p230_ax_fold_path row)->
 p230_ax_register_graph M env(p230_ax_fold_before row)start->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(ax_primitive_exit(fst row)) /\
 p230_ax_register_graph M env(p230_ax_fold_after row)final.
Definition p230_ax_fold_entry(rows:list p230_ax_fold_row)(exit:list bool):list bool:=
 match rows with []=>exit|row::_=>p230_ax_fold_path row end.
Fixpoint p230_ax_fold_connectors(rows:list p230_ax_fold_row)(exit:list bool):Prop:=
 match rows with []=>True|row::tail=>ipeq(ax_primitive_exit(fst row))(p230_ax_fold_entry tail exit) /\p230_ax_fold_connectors tail exit end.
Fixpoint p230_ax_fold_links(before:program230_configuration code_expr)(rows:list p230_ax_fold_row)(after:program230_configuration code_expr):Prop:=
 match rows with []=>before=after|row::tail=>p230_ax_fold_before row=before /\p230_ax_fold_links(p230_ax_fold_after row)tail after end.
Theorem p230_ax_finite_history_fold M env rows:
 Forall(p230_ax_runtime_row M env)rows->
 forall before after exit start entry,
 p230_ax_fold_links before rows after->p230_ax_fold_connectors rows exit->
 program230_pc start=program230_path_value M entry->ipeq entry(p230_ax_fold_entry rows exit)->
 p230_ax_register_graph M env before start->
 exists b c time final finalpath,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\
 program230_pc final=program230_path_value M finalpath /\ipeq finalpath exit /\
 p230_ax_register_graph M env after final /\(rows<>[]->coding_lt M(zeroM M)time).
Proof.
 intro Hrows;induction Hrows as[|row rows Hrow Hrows IH];intros before after exit start entry Hlink Hconn Hpc Hentry HG.
 -cbn[p230_ax_fold_links]in Hlink;subst after.
  destruct(p230_program_history_zero M start)as[b[c[HR HT]]].
  exists b,c,(zeroM M),start,entry;split;[exact HR|]. split;[exact HT|].
  split;[exact Hpc|]. split;[exact Hentry|]. split;[exact HG|intro H;contradiction].
 -destruct Hlink as[Hbefore Htail];destruct Hconn as[Hnext Hconnect].
  set(canonical:=program230_with_pc start(program230_path_value M(p230_ax_fold_path row))).
  assert(HGc:p230_ax_register_graph M env(p230_ax_fold_before row)canonical).
  {intros i Hi;unfold canonical;rewrite program230_with_pc_register,Hbefore;exact(HG i Hi). }
  destruct(Hrow canonical eq_refl HGc)as[b[c[N[mid[HR[HT[HN[HP HM]]]]]]]].
  destruct(p230_positive_history_entry M(p230_ax_fold_path row)entry canonical mid b c N eq_refl
  (ipeq_sym _ _ Hentry)HR HT HN)as[d[e[HD HTE]]].
  assert(E:program230_with_pc canonical(program230_path_value M entry)=start).
  {unfold canonical;rewrite program230_with_pc_twice;apply program230_with_pc_restore;exact Hpc. }
  rewrite E in HD.
  destruct(IH(p230_ax_fold_after row)after exit mid(ax_primitive_exit(fst row))Htail Hconnect HP Hnext HM)
  as[f[g[K[final[finalpath[HF[HTF[HPF[HEF[HGF Hpos]]]]]]]]]].
  destruct(p230_program_history_join M d e N f g K start mid HD HTE HF)as[u[v[HU[HL HH]]]].
  exists u,v,(addM M N K),final,finalpath;split;[exact HU|].
  split;[exact(proj1(HH K _(coding_lt_succ M K))HTF)|]. split;[exact HPF|].
  split;[exact HEF|]. split;[exact HGF|]. intros _;apply program230_positive_sum;exact HN.
Qed.
Print Assumptions p230_ax_finite_history_fold.
