(** Exact right-associated two-target affine-copy cycle in the published p230 tree. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230TransferCycle Program230TransferStates Program230ResetLoop.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_copy2_state {D} a b c(base:program230_configuration D)pc source y z:=
 program230_transfer_state a b(program230_transfer_state c c base pc z z)pc source y.
Lemma program230_copy2_pc {D} a b c(base:program230_configuration D)pc source y z:
 program230_pc(program230_copy2_state a b c base pc source y z) = pc.
Proof. reflexivity. Qed.
Lemma program230_copy2_register {D} a b c(base:program230_configuration D)pc source y z i:
 (i<9)%nat->program230_register(program230_copy2_state a b c base pc source y z)i =
 if Nat.eqb i a then source else if Nat.eqb i b then y else if Nat.eqb i c then z else program230_register base i.
Proof.
 intro Hi;unfold program230_copy2_state. rewrite !program230_transfer_register by exact Hi.
 destruct(Nat.eqb i a),(Nat.eqb i b),(Nat.eqb i c);reflexivity.
Qed.
Lemma program230_copy2_eval M rho a b c base pc source y z:
 program230_eval_config M rho(program230_copy2_state a b c base pc source y z) =
 program230_copy2_state a b c(program230_eval_config M rho base)(evalM M rho pc)
 (evalM M rho source)(evalM M rho y)(evalM M rho z).
Proof. unfold program230_copy2_state;now rewrite !program230_transfer_eval. Qed.
Lemma program230_copy2_restore {D} a b c(base:program230_configuration D)pc source y z:
 program230_pc base = pc->program230_register base a = source->program230_register base b = y->
 program230_register base c = z->program230_copy2_state a b c base pc source y z = base.
Proof.
 intros HP HA HB HC;apply program230_configuration_ext;intros j Hj.
 destruct j as[|j];[exact(eq_sym HP)|].
 change(program230_register(program230_copy2_state a b c base pc source y z)j = program230_register base j).
 rewrite program230_copy2_register by lia.
 destruct(Nat.eqb j a)eqn:Ea;[apply Nat.eqb_eq in Ea;subst j;exact(eq_sym HA)|].
 destruct(Nat.eqb j b)eqn:Eb;[apply Nat.eqb_eq in Eb;subst j;exact(eq_sym HB)|].
 destruct(Nat.eqb j c)eqn:Ec;[apply Nat.eqb_eq in Ec;subst j;exact(eq_sym HC)|reflexivity].
Qed.
Definition program230_control_leaf_formula source Q e:=
 $0==program230_path_term source ∧program230_record_edge_formula Q e.
Lemma program230_control_leaf_correct M source Q e s t:
 Program230Histories.program230_step M(program230_control_leaf_formula source Q e)s t<->
 program230_pc s = program230_path_value M source /\
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t).
Proof.
 unfold program230_control_leaf_formula,Program230Histories.program230_step.
 rewrite holds_and,program230_holds_equal,program230_path_term_correct.
 change((program230_pc s = program230_path_value M source /\
 Program230Histories.program230_step M(program230_record_edge_formula Q e)s t)<->
 program230_pc s = program230_path_value M source /\
 program230_edge_step M Q e(program230_register s)(program230_register t)(program230_pc t)).
 now rewrite program230_record_edge_formula_correct.
Qed.
Definition program230_copy2_formula P a b c:=
 program230_control_leaf_formula P(P++[false])(EDecnz a) ∨
 (program230_control_leaf_formula(P++[true])(P++[true;false])(EInc b) ∨
 (program230_control_leaf_formula(P++[true;true])(P++[true;true;false])(EInc c) ∨
 program230_control_leaf_formula(P++[true;true;true])(P++[true;true;true])(EContinue 3))).
Definition program230_copy2_cycle M P a b c s t:=
 (program230_pc s = program230_path_value M P /\
 program230_edge_step M(P++[false])(EDecnz a)(program230_register s)(program230_register t)(program230_pc t)) \/
 ((program230_pc s = program230_path_value M(P++[true]) /\
 program230_edge_step M(P++[true;false])(EInc b)(program230_register s)(program230_register t)(program230_pc t)) \/
 ((program230_pc s = program230_path_value M(P++[true;true]) /\
 program230_edge_step M(P++[true;true;false])(EInc c)(program230_register s)(program230_register t)(program230_pc t)) \/
 (program230_pc s = program230_path_value M(P++[true;true;true]) /\
 program230_edge_step M(P++[true;true;true])(EContinue 3)(program230_register s)(program230_register t)(program230_pc t)))).
Lemma program230_copy2_formula_correct M P a b c s t:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)s t<->program230_copy2_cycle M P a b c s t.
Proof.
 unfold program230_copy2_formula,program230_copy2_cycle,Program230Histories.program230_step.
 rewrite !holds_or.
 change((Program230Histories.program230_step M(program230_control_leaf_formula P(P++[false])(EDecnz a))s t \/
 (Program230Histories.program230_step M(program230_control_leaf_formula(P++[true])(P++[true;false])(EInc b))s t \/
 (Program230Histories.program230_step M(program230_control_leaf_formula(P++[true;true])(P++[true;true;false])(EInc c))s t \/
 Program230Histories.program230_step M(program230_control_leaf_formula(P++[true;true;true])(P++[true;true;true])(EContinue 3))s t)))<->
 program230_copy2_cycle M P a b c s t).
 now rewrite !program230_control_leaf_correct.
Qed.
Lemma program230_copy2_inc_first P:inc_path(P++[true;false]) = P++[true;true].
Proof. replace(P++[true;false])with((P++[true])++[false])by(repeat rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false. repeat rewrite <-app_assoc;reflexivity. Qed.
Lemma program230_copy2_inc_second P:inc_path(P++[true;true;false]) = P++[true;true;true].
Proof. replace(P++[true;true;false])with((P++[true;true])++[false])by(repeat rewrite <-app_assoc;reflexivity).
 rewrite inc_path_app_false. repeat rewrite <-app_assoc;reflexivity. Qed.
Section Steps.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Variables(P:list bool)(a b c:nat).
Hypotheses(Ha:(a<9)%nat)(Hb:(b<9)%nat)(Hc:(c<9)%nat)(Hab:a<>b)(Hac:a<>c)(Hbc:b<>c).
Local Notation cfg:=(program230_copy2_state a b c).
Ltac regs:=intros i Hi;rewrite !program230_copy2_register by exact Hi.
Ltac cases3 i:=destruct(Nat.eqb i a)eqn:Ea;destruct(Nat.eqb i b)eqn:Eb;destruct(Nat.eqb i c)eqn:Ec;
 try(apply Nat.eqb_eq in Ea);try(apply Nat.eqb_eq in Eb);try(apply Nat.eqb_eq in Ec);try congruence;try reflexivity.
Lemma program230_copy2_exit base y z:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)
 (cfg base(program230_path_value M P)Z y z)(cfg base(program230_path_value M(inc_path P))Z y z).
Proof. apply program230_copy2_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. left;split.
 -rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl.
 -split;[rewrite brk_car1;reflexivity|]. regs;reflexivity.
Qed.
Lemma program230_copy2_dec base n y z:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)
 (cfg base(program230_path_value M P)(S n)y z)(cfg base(program230_path_value M(P++[true]))n y z).
Proof. apply program230_copy2_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. right;exists n;split.
 -rewrite program230_copy2_register by exact Ha;now rewrite Nat.eqb_refl.
 -split;[rewrite inc_path_app_false;reflexivity|]. regs;destruct(Nat.eqb i a);reflexivity.
Qed.
Lemma program230_copy2_first base n y z:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)
 (cfg base(program230_path_value M(P++[true]))n y z)
 (cfg base(program230_path_value M(P++[true;true]))n(S y)z).
Proof. apply program230_copy2_formula_correct;right;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Hb|]. split;[rewrite program230_copy2_inc_first;reflexivity|].
 rewrite program230_copy2_register by exact Hb.
 rewrite(proj2(Nat.eqb_neq b a)ltac:(congruence)),Nat.eqb_refl.
 regs;cases3 i.
Qed.
Lemma program230_copy2_second base n y z:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)
 (cfg base(program230_path_value M(P++[true;true]))n y z)
 (cfg base(program230_path_value M(P++[true;true;true]))n y(S z)).
Proof. apply program230_copy2_formula_correct;right;right;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Hc|]. split;[rewrite program230_copy2_inc_second;reflexivity|].
 rewrite program230_copy2_register by exact Hc.
 rewrite(proj2(Nat.eqb_neq c a)ltac:(congruence)),(proj2(Nat.eqb_neq c b)ltac:(congruence)),Nat.eqb_refl.
 regs;cases3 i.
Qed.
Lemma program230_copy2_cont base n y z:
 Program230Histories.program230_step M(program230_copy2_formula P a b c)
 (cfg base(program230_path_value M(P++[true;true;true]))n y z)(cfg base(program230_path_value M P)n y z).
Proof. apply program230_copy2_formula_correct;right;right;right;split;[reflexivity|].
 cbn[program230_edge_step];split.
 -replace(P++[true;true;true])with(((P++[true])++[true])++[true])by(repeat rewrite <-app_assoc;reflexivity).
  rewrite !cont_cdrS,cont_cdr1;reflexivity.
 -regs;reflexivity.
Qed.
Theorem program230_copy2_four base n y z:exists u v,
 program230_history M(program230_copy2_formula P a b c)u v(N 4)
 (cfg base(program230_path_value M P)(S n)y z) /\
 program230_state_at M u v(N 4)(cfg base(program230_path_value M P)n(S y)(S z)).
Proof.
 destruct(program230_history_one M(program230_copy2_formula P a b c)_ _(program230_copy2_dec base n y z))as[u[v[HR HT]]].
 destruct(program230_history_extend M(program230_copy2_formula P a b c)u v(N 1)_ _ _ HR HT(program230_copy2_first base n y z))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M(program230_copy2_formula P a b c)d e(N 2)_ _ _ HD HE(program230_copy2_second base n(S y)z))as[f[g[HF[HG _]]]].
 destruct(program230_history_extend M(program230_copy2_formula P a b c)f g(N 3)_ _ _ HF HG(program230_copy2_cont base n(S y)(S z)))as[h[k[HH[HK _]]]].
 exists h,k;exact(conj HH HK).
Qed.
End Steps.
Print Assumptions program230_copy2_four.
