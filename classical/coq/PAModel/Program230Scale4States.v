(** Six real primitive steps of the four-increment loop. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230Edges Program230Configurations Program230Histories
 Program230HistoryConstructors Program230TransferCycle Program230TransferStates Program230ControlTable.
From K230 Require Import RM RMEquiv.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_scale4_pc P j:=P++match j with
 |0=>[true]|1=>[true;false;false;true]|2=>[true;false;true;false]
 |3=>[true;false;true;true]|_=>[true;true;false;false]end.
Definition program230_scale4_leaf P j:=if Nat.eqb j 0 then P++[true;false;false;false] else program230_scale4_pc P j.
Definition program230_scale4_rows P a b:list program230_control_row:=
 [((P,P++[false]),EDecnz a);
 ((program230_scale4_pc P 0,program230_scale4_leaf P 0),EInc b);
 ((program230_scale4_pc P 1,program230_scale4_leaf P 1),EInc b);
 ((program230_scale4_pc P 2,program230_scale4_leaf P 2),EInc b);
 ((program230_scale4_pc P 3,program230_scale4_leaf P 3),EInc b);
 ((program230_scale4_pc P 4,P++[true;true]),EContinue 2)].
Definition program230_scale4_formula P a b:=program230_control_table_formula(program230_scale4_rows P a b).
Lemma program230_scale4_increment_path P j:(j<4)%nat->
 inc_path(program230_scale4_leaf P j) = program230_scale4_pc P(S j).
Proof.
 intro Hj;destruct j as[|[|[|[|j]]]];try lia;
 unfold program230_scale4_leaf,program230_scale4_pc;cbn[Nat.eqb];
 unfold inc_path;rewrite rev_app_distr;cbn[rev inc_rev app];
 rewrite ?rev_app_distr,?rev_involutive;repeat rewrite <-app_assoc;reflexivity.
Qed.
Section Cycle.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Variables(P:list bool)(a b:nat).
Hypotheses(Ha:(a<9)%nat)(Hb:(b<9)%nat)(Hab:a<>b).
Local Notation cfg:=(program230_transfer_state a b).
Lemma program230_scale4_exit base y:
 Program230Histories.program230_step M(program230_scale4_formula P a b)
 (cfg base(program230_path_value M P)Z y)(cfg base(program230_path_value M(inc_path P))Z y).
Proof.
 apply(program230_control_table_intro M _ P(P++[false])(EDecnz a));[now left|reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. left;split;[apply program230_transfer_source;exact Ha|].
 split;[rewrite brk_car1;reflexivity|]. intros i Hi;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Lemma program230_scale4_dec base n y:
 Program230Histories.program230_step M(program230_scale4_formula P a b)
 (cfg base(program230_path_value M P)(S n)y)(cfg base(program230_path_value M(P++repeat true 1))n y).
Proof.
 apply(program230_control_table_intro M _ P(P++[false])(EDecnz a));[now left|reflexivity|].
 cbn[program230_edge_step];split;[exact Ha|]. right;exists n;split;[apply program230_transfer_source;exact Ha|].
 split;[rewrite inc_path_app_false;reflexivity|]. intros i Hi;rewrite !program230_transfer_register by exact Hi;
 destruct(Nat.eqb i a);reflexivity.
Qed.
Lemma program230_scale4_inc j base n y:(j<4)%nat->
 Program230Histories.program230_step M(program230_scale4_formula P a b)
 (cfg base(program230_path_value M(program230_scale4_pc P j))n y)
 (cfg base(program230_path_value M(program230_scale4_pc P(Datatypes.S j)))n(S y)).
Proof.
 intro Hj. apply(program230_control_table_intro M _(program230_scale4_pc P j)(program230_scale4_leaf P j)(EInc b)).
 -unfold program230_scale4_rows. destruct j as[|[|[|[|j]]]];try lia;cbn;tauto.
 -reflexivity.
 -cbn[program230_edge_step];split;[exact Hb|]. split;[rewrite program230_scale4_increment_path by exact Hj;reflexivity|].
  rewrite program230_transfer_target by assumption. intros i Hi;rewrite !program230_transfer_register by exact Hi.
  destruct(Nat.eqb i b)eqn:Eib;[apply Nat.eqb_eq in Eib;subst i|reflexivity].
  now rewrite(proj2(Nat.eqb_neq b a)ltac:(congruence)).
Qed.
Lemma program230_scale4_cont base n y:
 Program230Histories.program230_step M(program230_scale4_formula P a b)
 (cfg base(program230_path_value M(program230_scale4_pc P 4))n y)(cfg base(program230_path_value M P)n y).
Proof.
 apply(program230_control_table_intro M _(program230_scale4_pc P 4)(P++[true;true])(EContinue 2)).
 -unfold program230_scale4_rows;cbn;tauto.
 -reflexivity.
 -cbn[program230_edge_step];split;[replace(P++[true;true])with((P++[true])++[true])by(repeat rewrite <-app_assoc;reflexivity);rewrite cont_cdrS,cont_cdr1;reflexivity|].
  intros i Hi;rewrite !program230_transfer_register by exact Hi;reflexivity.
Qed.
Theorem program230_scale4_six base n y:exists u v,
 program230_history M(program230_scale4_formula P a b)u v(N 6)
 (cfg base(program230_path_value M P)(S n)y) /\
 program230_state_at M u v(N 6)(cfg base(program230_path_value M P)n(S(S(S(S y))))).
Proof.
 destruct(program230_history_one M(program230_scale4_formula P a b)_ _(program230_scale4_dec base n y))as[u[v[HR HT]]].
 destruct(program230_history_extend M(program230_scale4_formula P a b)u v(N 1)_ _ _ HR HT(program230_scale4_inc 0 base n y ltac:(lia)))as[d[e[HD[HE _]]]].
 destruct(program230_history_extend M(program230_scale4_formula P a b)d e(N 2)_ _ _ HD HE(program230_scale4_inc 1 base n(S y)ltac:(lia)))as[f[g[HF[HG _]]]].
 destruct(program230_history_extend M(program230_scale4_formula P a b)f g(N 3)_ _ _ HF HG(program230_scale4_inc 2 base n(S(S y))ltac:(lia)))as[h[k[HH[HK _]]]].
 destruct(program230_history_extend M(program230_scale4_formula P a b)h k(N 4)_ _ _ HH HK(program230_scale4_inc 3 base n(S(S(S y)))ltac:(lia)))as[l[m[HL[HM _]]]].
 destruct(program230_history_extend M(program230_scale4_formula P a b)l m(N 5)_ _ _ HL HM(program230_scale4_cont base n(S(S(S(S y))))))as[r[s[Hrun[Hlast _]]]].
 exists r,s;exact(conj Hrun Hlast).
Qed.
End Cycle.
Print Assumptions program230_scale4_six.
