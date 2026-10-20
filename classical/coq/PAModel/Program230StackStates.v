(** The four varying registers of stack construction, with an untouched frame. *)
From PAModel Require Import Program230Configurations Program230TransferStates Program230Copy2States.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.
Definition program230_stack_state {D}(base:program230_configuration D)pc tw ws s1 s2:=
 program230_copy2_state 1 2 6(program230_transfer_state 7 7 base pc s2 s2)pc tw ws s1.
Lemma program230_stack_pc {D}(base:program230_configuration D)pc tw ws s1 s2:
 program230_pc(program230_stack_state base pc tw ws s1 s2)=pc.
Proof. reflexivity. Qed.
Lemma program230_stack_register {D}(base:program230_configuration D)pc tw ws s1 s2 i:
 (i<9)%nat->program230_register(program230_stack_state base pc tw ws s1 s2)i=
 if Nat.eqb i 1 then tw else if Nat.eqb i 2 then ws else if Nat.eqb i 6 then s1 else
 if Nat.eqb i 7 then s2 else program230_register base i.
Proof.
 intro Hi;unfold program230_stack_state;rewrite program230_copy2_register,program230_transfer_register by exact Hi.
 destruct(Nat.eqb i 1),(Nat.eqb i 2),(Nat.eqb i 6),(Nat.eqb i 7);reflexivity.
Qed.
Lemma program230_stack_frame {D}(base out:program230_configuration D)pc tw ws s1 s2:
 program230_pc out=pc->program230_register out 1=tw->program230_register out 2=ws->
 program230_register out 6=s1->program230_register out 7=s2->
 (forall i,(i<9)%nat->i<>1->i<>2->i<>6->i<>7->program230_register out i=program230_register base i)->
 out=program230_stack_state base pc tw ws s1 s2.
Proof.
 intros HP H1 H2 H6 H7 HO;apply program230_configuration_ext;intros j Hj.
 destruct j as[|i];[exact HP|]. change(program230_register out i=program230_register(program230_stack_state base pc tw ws s1 s2)i).
 rewrite program230_stack_register by lia.
 destruct(Nat.eqb i 1)eqn:E1;[apply Nat.eqb_eq in E1;subst i;exact H1|].
 destruct(Nat.eqb i 2)eqn:E2;[apply Nat.eqb_eq in E2;subst i;exact H2|].
 destruct(Nat.eqb i 6)eqn:E6;[apply Nat.eqb_eq in E6;subst i;exact H6|].
 destruct(Nat.eqb i 7)eqn:E7;[apply Nat.eqb_eq in E7;subst i;exact H7|].
 apply HO;[lia|now apply Nat.eqb_neq|now apply Nat.eqb_neq|now apply Nat.eqb_neq|now apply Nat.eqb_neq].
Qed.
Lemma program230_stack_restore {D}(base:program230_configuration D):
 program230_stack_state base(program230_pc base)(program230_register base 1)(program230_register base 2)
 (program230_register base 6)(program230_register base 7)=base.
Proof. symmetry;apply program230_stack_frame;reflexivity. Qed.
Print Assumptions program230_stack_frame.
