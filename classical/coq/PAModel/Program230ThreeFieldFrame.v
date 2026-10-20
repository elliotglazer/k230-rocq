(** Canonical reconstruction of a finite register frame; no function extensionality. *)
From PAModel Require Import Program230Configurations Program230TransferStates Program230Copy2States.
From Stdlib Require Import Arith.Arith Lia.
Unset Implicit Arguments.
Lemma program230_three_field_frame {D} a b c(base out:program230_configuration D)pc x y z:
 program230_pc out = pc->program230_register out a = x->program230_register out b = y->
 program230_register out c = z->
 (forall i,(i<9)%nat->i<>a->i<>b->i<>c->program230_register out i = program230_register base i)->
 out = program230_copy2_state a b c base pc x y z.
Proof.
 intros HP HA HB HC HO;apply program230_configuration_ext;intros j Hj.
 destruct j as[|i];[exact HP|].
 change(program230_register out i = program230_register(program230_copy2_state a b c base pc x y z)i).
 rewrite program230_copy2_register by lia.
 destruct(Nat.eqb i a)eqn:Ea;[apply Nat.eqb_eq in Ea;subst i;exact HA|].
 destruct(Nat.eqb i b)eqn:Eb;[apply Nat.eqb_eq in Eb;subst i;exact HB|].
 destruct(Nat.eqb i c)eqn:Ec;[apply Nat.eqb_eq in Ec;subst i;exact HC|].
 apply HO;[lia|now apply Nat.eqb_neq|now apply Nat.eqb_neq|now apply Nat.eqb_neq].
Qed.
Print Assumptions program230_three_field_frame.
