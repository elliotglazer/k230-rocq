(** Actual generalization closure of the continuation compiler. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions NumericalProofs
 SearchStep NumericalCommands NumericalReachability NumericalSearchDrain ProgramRealizability
 NumericalRuntime RuntimeFiniteMacros.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Section Generalization.
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
Definition generalization_suffix (x:D):list(runtime_command M):=
 [Drop;Nip;Ax x x O O]++repeat Nip 9++[Drop;Nip;Nip].
Local Opaque runtime_wim runtime_bundle macro_r1 macro_r2 macro_r3 macro_r4
 macro_r5 macro_r6 macro_r7 macro_r8 macro_gen.
Lemma generalization_suffix_exec x h w:
 Exec(generalization_suffix x)(h,w,O,O)=Some(macro_gen M P x h,w,O,O).
Proof.
 unfold generalization_suffix.
 repeat first[progress cbn [repeat app]|rewrite (macro_ex_drop M P U E)|
 rewrite (macro_ex_ax M P U E)|
 rewrite (macro_ex_nip M P U E HP HU HE) by
  first[apply(macro_gen_ne1 M P HP)|apply(macro_row1_ne1 M P HP)|
  apply(macro_row2_ne1 M P HP)|apply(macro_row3_ne1 M P HP)|
  apply(macro_row4_ne1 M P HP)|apply(macro_row5_ne1 M P HP)|
  apply(macro_row6_ne1 M P HP)|apply(macro_row7_ne1 M P HP)|
  apply(macro_row8_ne1 M P HP)|apply zero_ne_succ]|
 rewrite (macro_stack_expand M P)|rewrite(macro_gate_same M P E HE)|
 rewrite coding_add_zero_r|rewrite coding_add_zero].
 reflexivity.
Qed.
Lemma runtime_generalization_graph x h:
 universal_graph M x h (macro_gen M P x h).
Proof. exact(runtime_value_graph M P HP _ _). Qed.
Theorem program_realizes_gen_using x h f:
 program_realizes M h ->universal_graph M x h f ->program_realizes M f.
Proof.
 intros Hh Hf.
 assert(Ef:macro_gen M P x h=f).
 { eapply code_relation_functional;[apply runtime_generalization_graph|exact Hf]. }
 intro tail. set(suffix:=runtime_program M P(generalization_suffix x)tail).
 destruct(Hh suffix)as[p Hp]. exists p. intros np t w.
 destruct(Hp np t w)as[Hhalt|Hrun];[now left|]. right.
 eapply numerical_reaches_transitive;[exact Hrun|].
 rewrite <-Ef.
 exact(runtime_exec_reaches M P U E HP HU HE (generalization_suffix x)
   (h,w,O,O)(macro_gen M P x h,w,O,O)tail np(generalization_suffix_exec x h w)).
Qed.
End Generalization.
Theorem program_realizes_gen M x h f:
 program_realizes M h ->universal_graph M x h f ->program_realizes M f.
Proof.
 intros Hh Hf. destruct(numerical_runtime_operations M)as[P[U[E[HP[HU HE]]]]].
 exact(program_realizes_gen_using M P U E HP HU HE x h f Hh Hf).
Qed.
Print Assumptions generalization_suffix_exec.
Print Assumptions program_realizes_gen.
