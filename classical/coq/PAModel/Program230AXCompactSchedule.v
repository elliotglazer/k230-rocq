(** Literal compact-DAG schedule for the AX constructors, stopping before the gate. *)
From PAModel Require Import CodeExpressions SearchStep Program230Configurations.
From K230 Require Import RM.
From K230P Require Import Dag230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_primitive(n:nat):bool:=existsb(Nat.eqb n)[166;121;168;171;177;119;181;180;182;218;178;183;176;158;208;192;131;211;197].
Fixpoint p230_ax_expand(fuel:nat)(e:edge):list edge:=
 match fuel with
 |0=>[e]
 |S k=>match e with ENode n=>if p230_ax_primitive n then[e]else
  p230_ax_expand k(fst(dag_nodes n))++p230_ax_expand k(snd(dag_nodes n))
 |_=>[e]end
 end.
Definition p230_ax_pre_gate_ids:list nat:=[166;121;180;176;168;171;158;208;119;166;119;166;168;119;121;168;119;119;119;168;166;182;168;121;182;166;121;182;119;119;166;166;168;180;183;168;119;168;166;182;168;121;181;166;121;181;119;119;166;121;168;180;180;121;166;168;180;180;119;166;121;182;168;166;181;168;121;181;119;119;166;121;168;119;180;166;121;180;166;168;180;119;119;166;166;121;182;183;168;168;121;168;181;119;121;121;168;181;166;168;166;168;168;166;181;168;121;181;119;180;121;168;121;168;121;168;181;178;183;119;180;119;180;178;183;119;180;178;183;166;121;181;168;166;121;181;180;119;166;121;182;168;166;121;182;180;119;178;178].
Theorem p230_ax_pre_gate_schedule:
 p230_ax_expand 200(ENode 236)=map ENode(p230_ax_pre_gate_ids++[192;131;211;197;131]).
Proof. vm_compute;reflexivity. Qed.
Theorem p230_ax_pre_gate_length:length p230_ax_pre_gate_ids=149.
Proof. reflexivity. Qed.
Print Assumptions p230_ax_pre_gate_schedule.
