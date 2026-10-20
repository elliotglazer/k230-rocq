(** Fixed finite runtime blocks.  Their operands range over arbitrary PA models. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
 NumericalProofs SearchStep NumericalCommands NumericalReachability NumericalSearchDrain
 ProgramRealizability NumericalRuntime NumericalCodeSeparation.
From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Section Macros.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation O:=(zeroM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Variable P:D->D->D.
Variable U:D->D*D.
Variable E:D->D->bool.
Hypothesis HP:forall a b,pair_graph M a b(P a b).
Hypothesis HU:forall z,pair_graph M(fst(U z))(snd(U z))z.
Hypothesis HE:forall a b,E a b=true <->a=b.
Local Notation Exec:=(runtime_exec M P U E).
Local Notation MP:=(runtime_wim M P).
Local Notation Gate:=(runtime_gate M P E).
Local Notation Stack:=(runtime_stack M P).
Local Notation Drop:=(Rdrop M).
Local Notation Nip:=(Rnip M).
Local Notation Cmp:=(Rcmp M).
Local Notation Ax:=(Rax M).
Local Notation RV:=(runtime_value M P).
Definition macro_env(a b c u:D):=code_parameters a b c u.
Definition macro_r1 a b:=RV(macro_env a b O O)code_row1.
Definition macro_r2 a b c:=RV(macro_env a b c O)code_row2.
Definition macro_r3 a b c:=RV(macro_env a b c O)code_row3.
Definition macro_r4 a b c:=RV(macro_env a b c O)code_row4.
Definition macro_r5 a b c:=RV(macro_env a b c O)code_row5.
Definition macro_r6 a c:=RV(macro_env a c O O)code_row6.
Definition macro_r7 a b c:=RV(macro_env a b c O)code_row7.
Definition macro_r8 a b c u:=RV(macro_env a b c u)code_row8.
Definition macro_gen a h:=RV(search_values M[a;h])(E_wal(CEvar 0)(CEvar 1)).

Lemma macro_stack_expand a h b c u t w:Stack a h b c u t w=
 P(macro_r1 a b)(P(macro_r2 a b c)(P(macro_r3 a b c)(P(macro_r4 a b c)
 (P(macro_r5 a b c)(P(macro_r6 a c)(P(macro_r7 a b c)(P(macro_r8 a b c u)
 (P(macro_gen a h)(P t w))))))))).
Proof. reflexivity. Qed.
Lemma macro_wim_nonzero t:MP t(N 1)<>O.
Proof.
 apply(search_implication_to_one_nonzero M t(MP t(N 1))).
 exact(runtime_value_graph M P HP _ _).
Qed.
Lemma macro_gate_same a b:Gate a b a=O.
Proof. unfold runtime_gate. rewrite(proj2(HE a a)eq_refl). reflexivity. Qed.
Lemma macro_gate_bundle a b c:c<>a->c<>b->Gate a b c=runtime_bundle M P a b c.
Proof.
 intros H1 H2. unfold runtime_gate. rewrite(proj2(runtime_eq_false M E HE c a)H1),
 (proj2(runtime_eq_false M E HE c b)H2). reflexivity.
Qed.
Lemma macro_gate_ne1 a b c:Gate a b c<>N 1.
Proof.
 destruct(runtime_gate_spec M P E HP HE a b c)as[[_ H]|[_[_ H]]].
 - rewrite H. apply zero_ne_succ.
 - exact(search_bundle_not_one M(search_values M[a;b;c])(CEvar 0)(CEvar 1)(CEvar 2)(Gate a b c)H).
Qed.
Lemma macro_row1_ne1 a b:macro_r1 a b<>N 1.
Proof. apply(search_rho1_not_one M(macro_env a b O O)(CEvar 0)(CEvar 1)(macro_r1 a b)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row2_ne1 a b c:macro_r2 a b c<>N 1.
Proof. apply(search_rho2_not_one M(macro_env a b c O)(CEvar 0)(CEvar 1)(CEvar 2)(macro_r2 a b c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row3_ne1 a b c:macro_r3 a b c<>N 1.
Proof. apply(search_rho3_not_one M(macro_env a b c O)(CEvar 0)(CEvar 1)(CEvar 2)(macro_r3 a b c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row4_ne1 a b c:macro_r4 a b c<>N 1.
Proof. apply(search_rho4_not_one M(macro_env a b c O)(CEvar 0)(CEvar 1)(CEvar 2)(macro_r4 a b c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row5_ne1 a b c:macro_r5 a b c<>N 1.
Proof. apply(search_rho5_not_one M(macro_env a b c O)(CEvar 0)(CEvar 1)(CEvar 2)(macro_r5 a b c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row6_ne1 a c:macro_r6 a c<>N 1.
Proof. apply(search_rho6_not_one M(macro_env a c O O)(CEvar 0)(CEvar 1)(macro_r6 a c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row7_ne1 a b c:macro_r7 a b c<>N 1.
Proof. apply(search_rho7_not_one M(macro_env a b c O)(CEvar 0)(CEvar 1)(CEvar 2)(macro_r7 a b c)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_row8_ne1 a b c u:macro_r8 a b c u<>N 1.
Proof. apply(search_rho8_not_one M(macro_env a b c u)(CEvar 0)(CEvar 1)(CEvar 2)(CEvar 3)(macro_r8 a b c u)). exact(runtime_value_graph M P HP _ _). Qed.
Lemma macro_gen_ne1 a h:macro_gen a h<>N 1.
Proof. apply(search_universal_not_one M a h). exact(runtime_value_graph M P HP _ _). Qed.

Lemma macro_ex_nip t x w d h L:h<>N 1->
 Exec(Nip::L)(t,P x w,d,h)=Exec L(t,w,d,x).
Proof.
 intro H. cbn [runtime_exec runtime_step].
 rewrite(proj2(runtime_eq_false M E HE h(N 1))H),(runtime_unpair M P U HP HU x w). reflexivity.
Qed.
Lemma macro_ex_drop t w d h L:Exec(Drop::L)(t,w,d,h)=Exec L(h,P t w,d,h).
Proof. reflexivity. Qed.
Lemma macro_ex_ax c x y u t w d h L:
 Exec(Ax c x y u::L)(t,w,d,h)=Exec L(Gate(d+x)(h+y)c,Stack(d+x)h(h+y)c u t w,O,O).
Proof. reflexivity. Qed.
Lemma macro_ex_mp_fail t x w d h L:MP t(d+x)<>h->
 Exec(Cmp x::L)(t,w,d,h)=Exec L(O,w,d+x,O).
Proof.
 intro H. cbn [runtime_exec runtime_step]. rewrite(proj2(runtime_eq_false M E HE _ _)H). reflexivity.
Qed.
Lemma macro_ex_mp_ok t x w d h L:MP t(d+x)=h->
 Exec(Cmp x::L)(t,w,d,h)=Exec L(d+x,P O w,d+x,O).
Proof.
 intro H. cbn [runtime_exec runtime_step]. rewrite(proj2(HE _ _)H). reflexivity.
Qed.
Lemma macro_exec_app L1 L2 q:Exec(L1++L2)q=
 match Exec L1 q with Some r=>Exec L2 r|None=>None end.
Proof. induction L1 in q|-*;cbn [runtime_exec app];[reflexivity|]. destruct(runtime_step M P U E a q);[apply IHL1|reflexivity]. Qed.

Local Opaque runtime_wim runtime_bundle macro_r1 macro_r2 macro_r3 macro_r4
 macro_r5 macro_r6 macro_r7 macro_r8 macro_gen.
Ltac macro_ne1:=first[apply macro_gate_ne1|apply macro_row1_ne1|apply macro_row2_ne1|
 apply macro_row3_ne1|apply macro_row4_ne1|apply macro_row5_ne1|apply macro_row6_ne1|
 apply macro_row7_ne1|apply macro_row8_ne1|apply macro_gen_ne1|apply zero_ne_succ].
Ltac macro_run:=repeat first[progress cbn [repeat app]|rewrite macro_ex_drop|
 rewrite macro_ex_ax|rewrite macro_ex_nip by macro_ne1|rewrite macro_stack_expand|
 rewrite macro_gate_same|rewrite coding_add_zero_r|rewrite coding_add_zero].

Definition macro_discard:list(runtime_command M):=[Cmp(N 1);Ax(N 1)O O O]++repeat Nip 10.
Lemma macro_discard_exec t w:Exec macro_discard(t,w,O,O)=Some(O,w,O,O).
Proof.
 unfold macro_discard. cbn [app]. rewrite macro_ex_mp_fail.
 - macro_run. reflexivity.
 - rewrite coding_add_zero. apply macro_wim_nonzero.
Qed.

Lemma finite_block_realizes f L:
 (forall t w,Exec L(t,w,O,O)=Some(f,w,O,O))->program_realizes M f.
Proof.
 intros H tail. exists(runtime_program M P L tail). intros np t w. right.
 exact(runtime_exec_reaches M P U E HP HU HE L(t,w,O,O)(f,w,O,O)tail np(H t w)).
Qed.
Theorem program_realizes_truth:program_realizes M O.
Proof. apply(finite_block_realizes O macro_discard). apply macro_discard_exec. Qed.
End Macros.
Print Assumptions macro_discard_exec.
Print Assumptions program_realizes_truth.





