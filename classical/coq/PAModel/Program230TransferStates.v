(** Finite actual transitions of the exact decrement/increment/continue cycle. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230TransferCycle.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_configuration_ext {D}(s t:program230_configuration D):
 (forall j,(j<10)%nat->program230_field s j = program230_field t j)->s = t.
Proof. destruct s,t;intro H;f_equal.
 -exact(H 0 ltac:(lia)).
 -exact(H 1 ltac:(lia)).
 -exact(H 2 ltac:(lia)).
 -exact(H 3 ltac:(lia)).
 -exact(H 4 ltac:(lia)).
 -exact(H 5 ltac:(lia)).
 -exact(H 6 ltac:(lia)).
 -exact(H 7 ltac:(lia)).
 -exact(H 8 ltac:(lia)).
 -exact(H 9 ltac:(lia)).
Qed.
Definition program230_transfer_state {D} a b (base:program230_configuration D) pc source target:=
 program230_config_of(fun j=>if Nat.eqb j 0 then pc else
 if Nat.eqb j(S a)then source else if Nat.eqb j(S b)then target else program230_field base j).
Lemma program230_transfer_pc {D} a b(base:program230_configuration D)pc source target:
 program230_pc(program230_transfer_state a b base pc source target) = pc.
Proof. reflexivity. Qed.
Lemma program230_transfer_register {D} a b(base:program230_configuration D)pc source target i:
 (i<9)%nat->program230_register(program230_transfer_state a b base pc source target)i = 
 if Nat.eqb i a then source else if Nat.eqb i b then target else program230_register base i.
Proof. intro H;unfold program230_register,program230_transfer_state.
 rewrite program230_config_of_fields by lia. reflexivity. Qed.
Lemma program230_transfer_source {D} a b(base:program230_configuration D)pc source target:
 (a<9)%nat->program230_register(program230_transfer_state a b base pc source target)a = source.
Proof. intro H;rewrite program230_transfer_register by exact H. now rewrite Nat.eqb_refl. Qed.
Lemma program230_transfer_target {D} a b(base:program230_configuration D)pc source target:
 (b<9)%nat->a<>b->program230_register(program230_transfer_state a b base pc source target)b = target.
Proof. intros H Hab;rewrite program230_transfer_register by exact H.
 assert(E:Nat.eqb b a = false)by(apply Nat.eqb_neq;congruence). now rewrite E,Nat.eqb_refl. Qed.
Lemma program230_transfer_state_restore {D} a b(base:program230_configuration D)pc source target:
 program230_pc base = pc->program230_register base a = source->program230_register base b = target->
 program230_transfer_state a b base pc source target = base.
Proof. intros HP HA HB. apply program230_configuration_ext;intros j Hj.
 unfold program230_transfer_state. rewrite program230_config_of_fields by exact Hj.
 destruct j as[|j];[exact(eq_sym HP)|]. cbn[Nat.eqb].
 destruct(Nat.eqb j a)eqn:Ea;[apply Nat.eqb_eq in Ea;subst j;exact(eq_sym HA)|].
 destruct(Nat.eqb j b)eqn:Eb;[apply Nat.eqb_eq in Eb;subst j;exact(eq_sym HB)|reflexivity]. Qed.
Lemma program230_transfer_eval M rho a b base pc source target:
 program230_eval_config M rho(program230_transfer_state a b base pc source target) = 
 program230_transfer_state a b(program230_eval_config M rho base)
 (evalM M rho pc)(evalM M rho source)(evalM M rho target).
Proof. apply program230_configuration_ext;intros j Hj.
 rewrite program230_eval_field by exact Hj. unfold program230_transfer_state.
 rewrite !program230_config_of_fields by exact Hj.
 destruct(Nat.eqb j 0), (Nat.eqb j(S a)),(Nat.eqb j(S b));try reflexivity.
 now rewrite program230_eval_field by exact Hj. Qed.
Section Transitions.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring transfer_state_ring:(model_semiring M).
Variables(P:list bool)(a b:nat).
Hypotheses(Ha:(a<9)%nat)(Hb:(b<9)%nat)(Hab:a<>b).
Local Notation cfg := (program230_transfer_state a b).
Lemma program230_transfer_exit base y:
 Program230Histories.program230_step M(program230_transfer_formula P a b)
 (cfg base(program230_path_value M P)Z y)
 (cfg base(program230_path_value M(inc_path P))Z y).
Proof. apply program230_transfer_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. left.
 split;[apply program230_transfer_source;exact Ha|]. split.
 -rewrite brk_car1;reflexivity.
 -intros i Hi;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Lemma program230_transfer_decrement base n y:
 Program230Histories.program230_step M(program230_transfer_formula P a b)
 (cfg base(program230_path_value M P)(S n)y)
 (cfg base(program230_path_value M(P++[true]))n y).
Proof. apply program230_transfer_formula_correct;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. right;exists n.
 split;[apply program230_transfer_source;exact Ha|]. split.
 -rewrite inc_path_app_false;reflexivity.
 -intros i Hi;rewrite !program230_transfer_register by exact Hi.
  destruct(Nat.eqb i a);reflexivity.
Qed.
Lemma program230_transfer_increment base n y:
 Program230Histories.program230_step M(program230_transfer_formula P a b)
 (cfg base(program230_path_value M(P++[true]))n y)
 (cfg base(program230_path_value M(P++[true;true]))n(S y)).
Proof. apply program230_transfer_formula_correct;right;left;split;[reflexivity|].
 cbn[program230_edge_step];split;[exact Hb|]. split.
 -replace(P++[true;false])with((P++[true])++[false])by (induction P as[|q Q IH];cbn;congruence).
  rewrite inc_path_app_false. change(program230_path_value M(P++[true;true]) = program230_path_value M((P++[true])++[true])). f_equal;exact(@List.app_assoc bool P (true::nil) (true::nil)).
 -intros i Hi;rewrite program230_transfer_target by assumption.
  rewrite !program230_transfer_register by exact Hi.
  destruct(Nat.eqb i b)eqn:Eib.
  +apply Nat.eqb_eq in Eib;subst i.
   assert(Eba:Nat.eqb b a = false)by(apply Nat.eqb_neq;congruence). now rewrite Eba.
  +reflexivity.
Qed.
Lemma program230_transfer_continue base n y:
 Program230Histories.program230_step M(program230_transfer_formula P a b)
 (cfg base(program230_path_value M(P++[true;true]))n y)
 (cfg base(program230_path_value M P)n y).
Proof. apply program230_transfer_formula_correct;right;right;split;[reflexivity|].
 cbn[program230_edge_step];split.
 -replace(P++[true;true])with((P++[true])++[true])by (induction P as[|q Q IH];cbn;congruence).
  rewrite cont_cdrS,cont_cdr1;reflexivity.
 -intros i Hi;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Theorem program230_transfer_three base n y:
 exists u v,program230_history M(program230_transfer_formula P a b)u v(N 3)
 (cfg base(program230_path_value M P)(S n)y) /\
 program230_state_at M u v(N 3)(cfg base(program230_path_value M P)n(S y)).
Proof.
 destruct(program230_history_one M(program230_transfer_formula P a b)_ _
 (program230_transfer_decrement base n y))as[u[v[Hrun Hlast]]].
 destruct(program230_history_extend M(program230_transfer_formula P a b)u v(N 1)_ _ _ Hrun Hlast
 (program230_transfer_increment base n y))as[d[e[Hrun2[Hlast2 _]]]].
 destruct(program230_history_extend M(program230_transfer_formula P a b)d e(N 2)_ _ _ Hrun2 Hlast2
 (program230_transfer_continue base n(S y)))as[f[g[Hrun3[Hlast3 _]]]].
 exists f,g;exact(conj Hrun3 Hlast3).
Qed.
End Transitions.
Print Assumptions program230_transfer_three.
