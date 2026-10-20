(** Every row of the exact AX trace has its actual positive arithmetic history. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions NumericalProofs
 Program230Configurations Program230PathCode Program230PushSites Program230ConsSites
 Program230AXSymbolic Program230AXSymbolicGraphs Program230AXNativeSymbolic Program230AXSymbolicTrace
 Program230AXPathSchedule Program230AXPrimitiveSchedule Program230AXSiteValidity
 Program230AXTypedNormalization Program230AXTypedTraceFacts Program230AXRowShapes Program230AXTransferBounds
 Program230AXRuntimeInterface Program230AXStackRuntime Program230AXMotionRuntime Program230AXReadSiteRuntime.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque p230_ax_typed_rows p230_ax_primitive_schedule p230_ax_schedule.
Lemma p230_ax_row_site item op before after:
 In(item,(op,before,after))p230_ax_typed_rows->In item p230_ax_primitive_schedule.
Proof. intro H;pose proof(in_map fst p230_ax_typed_rows (item,(op,before,after))H)as HM;rewrite p230_ax_typed_rows_positions in HM;exact HM. Qed.
Lemma p230_ax_site_actual_edge P e metadata:
 In((P,e),metadata)p230_ax_primitive_schedule ->fol p230(ENode(root p230))P=Some e.
Proof.
 intro H;assert(HP:In(P,e)p230_ax_schedule).
 {pose proof(in_map fst p230_ax_primitive_schedule((P,e),metadata)H)as HM;rewrite p230_ax_primitive_positions in HM;exact HM. }
 pose proof(proj1(forallb_forall _ _)p230_ax_schedule_all_positions(P,e)HP)as HE.
 unfold ax_site_position_valid in HE.
 destruct(fol p230(ENode(root p230))P)as[actual|]eqn:HF;[|discriminate].
 apply ax_edge_eqb_sound in HE;now subst actual.
Qed.
Lemma p230_ax_graph_zero M env before start i:
 p230_ax_register_graph M env before start ->(i<9)%nat ->
 program230_register before i=CEconst 0 ->program230_register start i=zeroM M.
Proof. intros HG Hi HE;pose proof(HG i Hi)as H;rewrite HE in H;exact H. Qed.
Local Opaque p230_ax_typed_rows p230_ax_primitive_schedule.
Theorem p230_ax_actual_typed_row M env item op before after:
 env 2=addM M(env 1)(env 11) ->pair_graph M(env 11)(env 9)(env 8) ->
 pair_graph M(env 4)(env 10)(env 9) ->In(item,(op,before,after))p230_ax_typed_rows ->
 forall start,program230_pc start=program230_path_value M(fst(fst item)) ->
 p230_ax_register_graph M env before start ->
 p230_ax_runtime_result M env after start(ax_primitive_exit item).
Proof.
 intros HE HP0 HP1 HI start HPC HG.
 pose proof(p230_ax_row_site item op before after HI)as Hsite.
 pose proof(proj1(Forall_forall _ _)p230_ax_primitive_sites_valid item Hsite)as HV.
 pose proof(p230_ax_typed_row_facts(item,(op,before,after))HI)as[HL[HS[HC[Hshape Hmeta]]]].
 destruct item as[[P e][typed index]].
 change(p230_ax_native_of typed=Some op)in HL.
 change(p230_ax_native_step op before=Some after)in HS.
 change(program230_pc start=program230_path_value M P)in HPC.
 destruct typed as[|r| |r|r|a b|a b c];cbn[p230_ax_native_of]in HL.
 -injection HL as <-;change(program230_register before 6=CEconst 0 /\program230_register before 7=CEconst 0)in HC.
  destruct HC as[HC6 HC7].
  change(Some(p230_ax_push before(CEconst 0))=Some after)in HS;injection HS as <-.
  change(match nth_error p230_push_site_rows index with Some(Q,n)=>P=Q /\e=ENode n|None=>False end)in HV.
  destruct(nth_error p230_push_site_rows index)as[[Q n]|]eqn:HN;[|contradiction].
  destruct HV as[-> _];apply p230_ax_runtime_push;try assumption.
  +exists n;eapply nth_error_In;exact HN.
  +exact(p230_ax_graph_zero M env before start 6 HG ltac:(lia)HC6).
  +exact(p230_ax_graph_zero M env before start 7 HG ltac:(lia)HC7).
 -injection HL as <-;change(program230_register before 6=CEconst 0 /\program230_register before 7=CEconst 0)in HC.
  change(program230_register before 1=CEconst 0 /\(r=3 \/r=4 \/r=5))in Hshape.
  apply(p230_ax_load_site_runtime M env before after start P e r index HV HPC);try assumption.
  +exact(p230_ax_graph_zero M env before start 6 HG ltac:(lia)(proj1 HC)).
  +exact(proj1 Hshape).
 -injection HL as <-;change(program230_register before 6=CEconst 0 /\program230_register before 7=CEconst 0)in HC.
  change(exists x tail,program230_register before 2=CEpair x tail)in Hshape.
  destruct Hshape as[x[tail Hstack]].
  change(p230_ax_binary E_wim before=Some after)in HS;unfold p230_ax_binary in HS;rewrite Hstack in HS;injection HS as <-.
  change(match nth_error p230_cons_sites index with Some site=>P=cons_path site /\e=ENode(cons_node site)|None=>False end)in HV.
  destruct(nth_error p230_cons_sites index)as[site|]eqn:HN;[|contradiction].
  destruct HV as[-> _];apply(p230_ax_runtime_cons M env before start site x tail);try assumption.
  +eapply nth_error_In;exact HN.
  +exact(p230_ax_graph_zero M env before start 6 HG ltac:(lia)(proj1 HC)).
  +exact(p230_ax_graph_zero M env before start 7 HG ltac:(lia)(proj2 HC)).
 -destruct r as[|[|r]];try discriminate HL;injection HL as <-.
  change(Some(p230_ax_set before 1(p230_ax_native_succ(program230_register before 1)))=Some after)in HS;injection HS as <-.
  change(e=EInc 1)in HV;subst e;apply p230_ax_runtime_increment;try assumption.
  exact(p230_ax_site_actual_edge P(EInc 1)(AIncrement 1,index)Hsite).
 -do 8(destruct r as[|r];[discriminate HL|]);destruct r as[|r];[|discriminate HL].
  injection HL as <-;change(program230_register before 6=CEconst 0 /\program230_register before 7=CEconst 0)in HC.
  change(program230_register before 8=CEvar 8 \/program230_register before 8=CEvar 9)in Hshape.
  apply(p230_ax_unpair_site_runtime M env before after start P e index HV HPC);try assumption.
  +exact(p230_ax_graph_zero M env before start 6 HG ltac:(lia)(proj1 HC)).
  +exact(p230_ax_graph_zero M env before start 7 HG ltac:(lia)(proj2 HC)).
 -injection HL as <-.
  destruct(p230_ax_typed_transfer_bounds((P,e),(ATransfer a b,index))a b before after HI)as[Ha[Hb Hab]].
  change(Some(p230_ax_set(p230_ax_set before b(p230_ax_native_add(program230_register before b)(program230_register before a)))a(CEconst 0))=Some after)in HS;injection HS as <-.
  change(match e with ENode n=>Program230TransferProgram.program230_transfer_occurrence p230 P a b n(S n)|_=>False end)in HV.
  destruct e as[n|r|r|k|k|];[|exact(False_rect _ HV)|exact(False_rect _ HV)|exact(False_rect _ HV)|exact(False_rect _ HV)|exact(False_rect _ HV)].
  apply(p230_ax_runtime_transfer M env before start P a b n(S n));assumption.
 -discriminate HL.
Qed.
Print Assumptions p230_ax_actual_typed_row.
