(** Exact logical/physical register permutation and effect decoding. *)
From PAModel Require Import Model Arithmetic FiniteCoding TM230RegisterWords TM230RegisterPrefix
 TM230RuntimeBox TM230RuntimeBoxProperties TM230SpareSyntax Program230Edges.
From K230 Require Interpreter230Check.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_physical_values M(R:nat->carrier M):list(carrier M):=
 map R machine230_physical_order.
Definition machine230_physical_index:=K230.Interpreter230Check.phys_of.
Lemma machine230_physical_length M R:length(machine230_physical_values M R)=9%nat.
Proof. reflexivity. Qed.
Lemma machine230_physical_nth M R r:
 (r<9)%nat->nth(machine230_physical_index r)(machine230_physical_values M R)(zeroM M)=R r.
Proof. intro H;do 9(destruct r as[|r];[reflexivity|]);lia. Qed.
Lemma machine230_physical_nth_error M R r:
 (r<9)%nat->nth_error(machine230_physical_values M R)(machine230_physical_index r)=Some(R r).
Proof. intro H;do 9(destruct r as[|r];[reflexivity|]);lia. Qed.
Lemma machine230_physical_index_bound r:(r<9)%nat->(machine230_physical_index r<9)%nat.
Proof. intro H;do 9(destruct r as[|r];[cbn;lia|]);lia. Qed.
Lemma machine230_physical_update_literal M R r value:
 (r<9)%nat->machine230_update_values(machine230_physical_index r)value(machine230_physical_values M R)=
 machine230_physical_values M(fun i=>if Nat.eqb i r then value else R i).
Proof. intro H;do 9(destruct r as[|r];[reflexivity|]);lia. Qed.
Lemma machine230_physical_list_ext M R T:
 (forall i,(i<9)%nat->R i=T i)->machine230_physical_values M R=machine230_physical_values M T.
Proof.
 intro H;unfold machine230_physical_values;apply map_ext_in;intros i Hi;apply H.
 cbn[machine230_physical_order]in Hi;repeat destruct Hi as[Hi|Hi];try contradiction;subst;lia.
Qed.
Theorem machine230_logical_physical_update M R T r value:
 (r<9)%nat->program230_register_update M r value R T ->
 machine230_update_values(machine230_physical_index r)value(machine230_physical_values M R)=
 machine230_physical_values M T.
Proof.
 intros Hr HU. rewrite(machine230_physical_update_literal M R r value Hr).
 apply machine230_physical_list_ext;intros i Hi;symmetry;exact(HU i Hi).
Qed.
Theorem machine230_register_file_list M R spare word:
 machine230_register_file M R spare word <->machine230_blocks_list M(machine230_physical_values M R)spare word.
Proof.
 unfold machine230_register_file,machine230_physical_values,machine230_physical_register,machine230_physical_order.
 reflexivity.
Qed.
Theorem machine230_logical_increment_effect M R T r:
 (r<9)%nat->program230_register_update M r(succM M(R r))R T ->
 machine230_effect_values M(Runtime230.FInc(machine230_physical_index r))
  (machine230_physical_values M R)(machine230_physical_values M T).
Proof.
 intros Hr HU;exists(R r);split;[exact(machine230_physical_nth_error M R r Hr)|].
 symmetry;exact(machine230_logical_physical_update M R T r(succM M(R r))Hr HU).
Qed.
Theorem machine230_logical_decrement_effect M R T r value:
 (r<9)%nat->R r=succM M value->program230_register_update M r value R T ->
 machine230_effect_values M(Runtime230.FDec(machine230_physical_index r))
  (machine230_physical_values M R)(machine230_physical_values M T).
Proof.
 intros Hr HE HU;exists(R r),value;split;[exact(machine230_physical_nth_error M R r Hr)|].
 split;[right;exact HE|]. symmetry;exact(machine230_logical_physical_update M R T r value Hr HU).
Qed.
Theorem machine230_box_effect_plain M values updated E eff word:
 machine230_effect_values M eff values updated ->machine230_runtime_box M values E(Runtime230.BPlain eff)word ->
 machine230_runtime_box M updated(match eff with Runtime230.FInc _=>succM M E|_=>E end)
  (Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros HU[HL[HE[actual[spare[HA[HS HW]]]]]].
 assert(EA:actual=updated)by(eapply machine230_effect_values_unique;eassumption). subst actual.
 split.
 -rewrite(machine230_effect_length M eff values updated HU);exact HL.
 -split.
  +destruct eff;try exact HE;apply coding_zero_lt_succ.
  +exists updated,spare;split;[reflexivity|]. split;assumption.
Qed.
Theorem machine230_logical_increment_box M R T r E word:
 (r<9)%nat->program230_register_update M r(succM M(R r))R T ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain(Runtime230.FInc(machine230_physical_index r)))word ->
 machine230_runtime_box M(machine230_physical_values M T)(succM M E)(Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros Hr HU HB;exact(machine230_box_effect_plain M _ _ E _ word(machine230_logical_increment_effect M R T r Hr HU)HB).
Qed.
Theorem machine230_logical_decrement_box M R T r value E word:
 (r<9)%nat->R r=succM M value->program230_register_update M r value R T ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain(Runtime230.FDec(machine230_physical_index r)))word ->
 machine230_runtime_box M(machine230_physical_values M T)E(Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros Hr HE HU HB;exact(machine230_box_effect_plain M _ _ E _ word(machine230_logical_decrement_effect M R T r value Hr HE HU)HB).
Qed.
Theorem machine230_logical_same_box M R T E word:
 program230_register_same M R T ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)word ->
 machine230_runtime_box M(machine230_physical_values M T)E(Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros HS HB. assert(EP:machine230_physical_values M T=machine230_physical_values M R).
 {apply machine230_physical_list_ext;exact HS. } now rewrite EP.
Qed.
Theorem machine230_physical_branch M R r z:
 (r<9)%nat->(machine230_runtime_branch_valid M(machine230_physical_values M R)(Some(machine230_physical_index r,z))<->
 if z then R r=zeroM M else R r<>zeroM M).
Proof. intro Hr;unfold machine230_runtime_branch_valid;destruct z;now rewrite(machine230_physical_nth M R r Hr). Qed.
Theorem machine230_register_box_intro M R E spare word:
 coding_lt M(zeroM M)E->machine230_spare M E spare->machine230_register_file M R spare word ->
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)word.
Proof.
 intros HE Hsp Hfile;split;[reflexivity|]. split;[exact HE|].
 exists(machine230_physical_values M R),spare;split;[reflexivity|]. split;[exact Hsp|].
 exact(proj1(machine230_register_file_list M R spare word)Hfile).
Qed.
Print Assumptions machine230_logical_physical_update.
Print Assumptions machine230_register_file_list.
Print Assumptions machine230_logical_increment_box.
Print Assumptions machine230_logical_decrement_box.
Print Assumptions machine230_logical_same_box.
Print Assumptions machine230_physical_branch.
Print Assumptions machine230_register_box_intro.
