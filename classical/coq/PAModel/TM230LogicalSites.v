(** Every checked nonhalting public program edge is a genuine positive path
    of the literal machine, with the exact updated logical register file. *)
From PAModel Require Import Model CodeExpressions TM230BinaryStep TM230MacroProgress
 TM230RuntimeBox TM230RuntimeSites TM230RuntimeSiteTargets TM230DispatchWords TM230ConcreteSites
 TM230PhysicalRegisters Program230PathCode Program230Edges.
From K230 Require RM Interpreter230Check Interpreter230Sites.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Unset Implicit Arguments.
Definition machine230_edge_path bits(e:K230.RM.edge)(z:bool):=
 match e with
 |K230.RM.EInc _=>K230.RM.inc_path bits
 |K230.RM.EDecnz _=>if z then K230.RM.brk 1 bits else K230.RM.inc_path bits
 |K230.RM.EBreak k=>K230.RM.brk k bits
 |K230.RM.EContinue k=>K230.RM.cont k bits
 |_=>bits end.
Definition machine230_edge_overflow bits(e:K230.RM.edge)(z:bool):=
 match e with
 |K230.RM.EInc _=>Sites230.allones bits
 |K230.RM.EDecnz _=>if z then Sites230.allones(K230.RM.strip_path false 1 bits)else Sites230.allones bits
 |K230.RM.EBreak k=>Sites230.allones(K230.RM.strip_path false k bits)
 |_=>false end.
Definition machine230_edge_boundary(e:K230.RM.edge)(z:bool):nat:=
 match e with K230.RM.EDecnz _=>if z then 0 else 1|_=>0 end.
Definition machine230_edge_spares M(e:K230.RM.edge)E:=
 match e with K230.RM.EInc _=>succM M E|_=>E end.
Theorem machine230_checked_program_edge M Q e R T pc' E gap input s:
 K230.Interpreter230Check.check_edge Q e=true ->program230_edge_step M Q e R T pc' ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)input ->
 machine230_dispatch_view M Q gap(Sites230.D0-length Q)input s ->
 exists z output t,pc'=program230_path_value M(machine230_edge_path Q e z) /\
 machine230_runtime_box M(machine230_physical_values M T)(machine230_edge_spares M e E)(Runtime230.BPlain Runtime230.FNone)output /\
 machine230_dispatch_view M(machine230_edge_path Q e z)gap
  (Sites230.D0+(if machine230_edge_overflow Q e z then 1 else 0)+machine230_edge_boundary e z-length(machine230_edge_path Q e z))output t /\
 machine230_progresses M s t.
Proof.
 intros HC HE HX HS. destruct e as[node|r|r|k|k|];cbn[program230_edge_step]in HE;try contradiction.
 -destruct HE as[Hr[Hpc HU]].
  unfold K230.Interpreter230Check.check_edge in HC.
  destruct(Nat.leb(length Q)40);[|discriminate]. destruct(Nat.ltb r 9);[|discriminate].
  assert(C:Sites230.run_to None Q(Sites230.tgt_conf(K230.RM.inc_path Q)(Sites230.allones Q)
   (Runtime230.BPlain(Runtime230.FInc(machine230_physical_index r))))=true).
  {exact(machine230_checked_site_target Q(Sites230.OInc(machine230_physical_index r))false _ HC eq_refl). }
  destruct(machine230_concrete_dispatch_site M(machine230_physical_values M R)E None Q
   (K230.RM.inc_path Q)(Sites230.allones Q)(Runtime230.BPlain(Runtime230.FInc(machine230_physical_index r)))
   gap input s I C HX HS)as[output[t[HB[HV HP]]]].
  exists false,output,t;split;[exact Hpc|]. split.
  +exact(machine230_logical_increment_box M R T r E output Hr HU HB).
  +split;assumption.
 -destruct HE as[Hr[HZ|[value[HR[Hpc HU]]]]].
  +destruct HZ as[HR[Hpc HT]].
   unfold K230.Interpreter230Check.check_edge in HC.
   destruct(Nat.leb(length Q)40);[|discriminate]. destruct(Nat.ltb r 9);[|discriminate].
   assert(C:Sites230.run_to(Some(machine230_physical_index r,true))Q
    (Sites230.tgt_conf(K230.RM.brk 1 Q)(Sites230.allones(K230.RM.strip_path false 1 Q))(Runtime230.BPlain Runtime230.FNone))=true).
   {exact(machine230_checked_site_target Q(Sites230.ODec(machine230_physical_index r))true _ HC eq_refl). }
   assert(B:machine230_runtime_branch_valid M(machine230_physical_values M R)(Some(machine230_physical_index r,true))).
   {apply(proj2(machine230_physical_branch M R r true Hr));exact HR. }
   destruct(machine230_concrete_dispatch_site M(machine230_physical_values M R)E _ Q
    (K230.RM.brk 1 Q)(Sites230.allones(K230.RM.strip_path false 1 Q))(Runtime230.BPlain Runtime230.FNone)
    gap input s B C HX HS)as[output[t[HB[HV HP]]]].
   exists true,output,t;split;[exact Hpc|]. split.
   *exact(machine230_logical_same_box M R T E output HT HB).
   *split;assumption.
  +unfold K230.Interpreter230Check.check_edge in HC.
   destruct(Nat.leb(length Q)40);[|discriminate]. destruct(Nat.ltb r 9);[|discriminate].
   assert(C:Sites230.run_to(Some(machine230_physical_index r,false))Q
    (Sites230.tgt_conf(K230.RM.inc_path Q)(Sites230.allones Q)(Runtime230.BPlain(Runtime230.FDec(machine230_physical_index r))))=true).
   {exact(machine230_checked_site_target Q(Sites230.ODec(machine230_physical_index r))false _ HC eq_refl). }
   assert(B:machine230_runtime_branch_valid M(machine230_physical_values M R)(Some(machine230_physical_index r,false))).
   {apply(proj2(machine230_physical_branch M R r false Hr));intro Ezero.
    exact(zero_ne_succ M value ltac:(congruence)). }
   destruct(machine230_concrete_dispatch_site M(machine230_physical_values M R)E _ Q
    (K230.RM.inc_path Q)(Sites230.allones Q)(Runtime230.BPlain(Runtime230.FDec(machine230_physical_index r)))
    gap input s B C HX HS)as[output[t[HB[HV HP]]]].
   exists false,output,t;split;[exact Hpc|]. split.
   *exact(machine230_logical_decrement_box M R T r value E output Hr HR HU HB).
   *split;assumption.
 -destruct HE as[Hpc HT]. unfold K230.Interpreter230Check.check_edge in HC.
  destruct(Nat.leb(length Q)40);[|discriminate].
  assert(C:Sites230.run_to None Q(Sites230.tgt_conf(K230.RM.brk k Q)
   (Sites230.allones(K230.RM.strip_path false k Q))(Runtime230.BPlain Runtime230.FNone))=true).
  {exact(machine230_checked_site_target Q(Sites230.OBrk k)false _ HC eq_refl). }
  destruct(machine230_concrete_dispatch_site M(machine230_physical_values M R)E None Q
   (K230.RM.brk k Q)(Sites230.allones(K230.RM.strip_path false k Q))(Runtime230.BPlain Runtime230.FNone)
   gap input s I C HX HS)as[output[t[HB[HV HP]]]].
  exists false,output,t;split;[exact Hpc|]. split.
  +exact(machine230_logical_same_box M R T E output HT HB).
  +split;assumption.
 -destruct HE as[Hpc HT]. unfold K230.Interpreter230Check.check_edge in HC.
  destruct(Nat.leb(length Q)40);[|discriminate].
  assert(C:Sites230.run_to None Q(Sites230.tgt_conf(K230.RM.cont k Q)false(Runtime230.BPlain Runtime230.FNone))=true).
  {exact(machine230_checked_site_target Q(Sites230.OCont k)false _ HC eq_refl). }
  destruct(machine230_concrete_dispatch_site M(machine230_physical_values M R)E None Q
   (K230.RM.cont k Q)false(Runtime230.BPlain Runtime230.FNone)gap input s I C HX HS)as[output[t[HB[HV HP]]]].
  exists false,output,t;split;[exact Hpc|]. split.
  +exact(machine230_logical_same_box M R T E output HT HB).
  +split;assumption.
Qed.
Print Assumptions machine230_checked_program_edge.



