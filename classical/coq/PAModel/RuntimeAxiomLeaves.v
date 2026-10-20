(** Every logical and K axiom has an actual finite continuation block. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
 NumericalProofs SearchStep NumericalCommands NumericalReachability NumericalSearchDrain
 ProgramRealizability NumericalRuntime NumericalCodeSeparation RuntimeFiniteMacros.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.
Unset Implicit Arguments.
Section Leaves.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation O:=(zeroM M).
Local Notation N:=(code_numeral M).
Variable P:D->D->D.
Variable U:D->D*D.
Variable E:D->D->bool.
Hypothesis HP:forall a b,pair_graph M a b(P a b).
Hypothesis HU:forall z,pair_graph M(fst(U z))(snd(U z))z.
Hypothesis HE:forall a b,E a b=true <->a=b.
Local Notation Exec:=(runtime_exec M P U E).
Local Notation Drop:=(Rdrop M).
Local Notation Nip:=(Rnip M).
Local Notation Ax:=(Rax M).
Definition axiom_leaf j a b c u:list(runtime_command M):=
 macro_discard M++[Ax c a b u]++repeat Nip j++[Drop]++repeat Nip(11-j).
Definition bundle_leaf a b c:list(runtime_command M):=
 macro_discard M++[Ax c a b O]++repeat Nip 10.
Local Opaque runtime_wim runtime_bundle macro_r1 macro_r2 macro_r3 macro_r4 macro_r5 macro_r6 macro_r7 macro_r8 macro_gen.
Ltac leaf_run:=
 unfold axiom_leaf;rewrite (macro_exec_app M P U E),(macro_discard_exec M P U E HP HU HE);
 repeat first[progress cbn [repeat app Nat.sub]|rewrite macro_ex_drop|rewrite macro_ex_ax|
 rewrite macro_ex_nip by (first[assumption|apply macro_gate_ne1;assumption|apply macro_row1_ne1;assumption|
 apply macro_row2_ne1;assumption|apply macro_row3_ne1;assumption|apply macro_row4_ne1;assumption|
 apply macro_row5_ne1;assumption|apply macro_row6_ne1;assumption|apply macro_row7_ne1;assumption|
 apply macro_row8_ne1;assumption|apply macro_gen_ne1;assumption|apply zero_ne_succ])|
 rewrite macro_stack_expand|rewrite coding_add_zero_r|rewrite coding_add_zero];reflexivity.

Lemma axiom_leaf1_exec a b c u t w:
 Exec(axiom_leaf 1 a b c u)(t,w,O,O)=Some(macro_r1 M P a b,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf2_exec a b c u t w:
 Exec(axiom_leaf 2 a b c u)(t,w,O,O)=Some(macro_r2 M P a b c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf3_exec a b c u t w:
 Exec(axiom_leaf 3 a b c u)(t,w,O,O)=Some(macro_r3 M P a b c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf4_exec a b c u t w:
 Exec(axiom_leaf 4 a b c u)(t,w,O,O)=Some(macro_r4 M P a b c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf5_exec a b c u t w:
 Exec(axiom_leaf 5 a b c u)(t,w,O,O)=Some(macro_r5 M P a b c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf6_exec a b c u t w:
 Exec(axiom_leaf 6 a b c u)(t,w,O,O)=Some(macro_r6 M P a c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf7_exec a b c u t w:
 Exec(axiom_leaf 7 a b c u)(t,w,O,O)=Some(macro_r7 M P a b c,w,O,O).
Proof. leaf_run. Qed.
Lemma axiom_leaf8_exec a b c u t w:
 Exec(axiom_leaf 8 a b c u)(t,w,O,O)=Some(macro_r8 M P a b c u,w,O,O).
Proof. leaf_run. Qed.
Lemma bundle_leaf_exec a b c t w:c<>a->c<>b->
 Exec(bundle_leaf a b c)(t,w,O,O)=Some(runtime_bundle M P a b c,w,O,O).
Proof.
 intros H1 H2. unfold bundle_leaf.
 rewrite(macro_exec_app M P U E),(macro_discard_exec M P U E HP HU HE).
 repeat first[progress cbn [repeat app Nat.sub]|rewrite macro_ex_ax|
 rewrite macro_ex_nip by (first[assumption|apply macro_row1_ne1;assumption|apply macro_row2_ne1;assumption|
 apply macro_row3_ne1;assumption|apply macro_row4_ne1;assumption|apply macro_row5_ne1;assumption|
 apply macro_row6_ne1;assumption|apply macro_row7_ne1;assumption|apply macro_row8_ne1;assumption|
 apply macro_gen_ne1;assumption|apply zero_ne_succ])|
 rewrite macro_stack_expand|rewrite coding_add_zero_r|rewrite coding_add_zero].
 rewrite(macro_gate_bundle M P E HE a b c H1 H2). reflexivity.
Qed.

Theorem runtime_axiom_realizes f:K230_axiom_relation M f->program_realizes M f.
Proof.
 intros[Hz|[a[b[c[u H]]]]].
 - subst f. exact(program_realizes_truth M P U E HP HU HE).
 - unfold code_axiom_rows in H.
   destruct H as[H|[H|[H|[H|[H|[H|[H|[H|[Ha[Hb H]]]]]]]]]].
   + assert(Hf:f=macro_r1 M P a b).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 1 a b c u)). apply axiom_leaf1_exec.
   + assert(Hf:f=macro_r2 M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 2 a b c u)). apply axiom_leaf2_exec.
   + assert(Hf:f=macro_r3 M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 3 a b c u)). apply axiom_leaf3_exec.
   + assert(Hf:f=macro_r4 M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 4 a b c u)). apply axiom_leaf4_exec.
   + assert(Hf:f=macro_r5 M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 5 a b c u)). apply axiom_leaf5_exec.
   + assert(Hf:f=macro_r6 M P a b).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 6 a O b u)). apply axiom_leaf6_exec.
   + assert(Hf:f=macro_r7 M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 7 a b c u)). apply axiom_leaf7_exec.
   + assert(Hf:f=macro_r8 M P a b c u).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (axiom_leaf 8 a b c u)). apply axiom_leaf8_exec.
   + assert(Hf:f=runtime_bundle M P a b c).
     { eapply code_relation_functional;[exact H|exact(runtime_value_graph M P HP _ _)]. }
     rewrite Hf. apply(finite_block_realizes M P U E HP HU HE _ (bundle_leaf a b c)).
     intros t w. apply bundle_leaf_exec;assumption.
Qed.
End Leaves.
Print Assumptions runtime_axiom_realizes.




Theorem numerical_axiom_program_realizes M f:
  K230_axiom_relation M f -> program_realizes M f.
Proof.
  intro H.
  destruct(numerical_runtime_operations M)as[P[U[E[HP[HU HE]]]]].
  exact(runtime_axiom_realizes M P U E HP HU HE f H).
Qed.
Print Assumptions numerical_axiom_program_realizes.
