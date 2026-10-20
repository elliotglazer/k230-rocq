(** Ordinary PA graphs for the exact public RM leaf actions. The path supplied
    here is the read prefix selected by RM.walk, not an unnormalized old PC. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 NumericalProofs Program230PathCode.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint program230_all_formula n(F:nat->form):form:=
 match n with 0=>zero==zero|S n=>F n ∧program230_all_formula n F end.
Lemma program230_all_formula_correct M rho n F:
 holds M rho(program230_all_formula n F)<->forall i,(i<n)%nat->holds M rho(F i).
Proof.
 induction n as[|n IH].
 -split;[intros _ i Hi;lia|intros _;reflexivity].
 -cbn[program230_all_formula];rewrite holds_and,IH. split.
  +intros[Hn Hrest]i Hi;destruct(Nat.eq_dec i n)as[->|Hne];[exact Hn|apply Hrest;lia].
  +intro H;split;[apply H;lia|intros i Hi;apply H;lia].
Qed.
Definition program230_register_same M(R T:nat->carrier M):Prop:=
 forall i,(i<9)%nat->T i = R i.
Definition program230_register_update M r value(R T:nat->carrier M):Prop:=
 forall i,(i<9)%nat->T i = if Nat.eqb i r then value else R i.
Definition program230_same_formula(before after:nat->term):form:=
 program230_all_formula 9(fun i => after i == before i).
Definition program230_update_formula(before after:nat->term)r(value:term):form:=
 program230_all_formula 9(fun i => after i == (if Nat.eqb i r then value else before i)).
Lemma program230_holds_equal M rho t u:holds M rho(t==u)<->evalM M rho t=evalM M rho u.
Proof. reflexivity. Qed.
Lemma program230_eval_up M rho x t:evalM M(x.:rho)t`[↑]=evalM M rho t.
Proof. unfold evalM;now rewrite eval_up. Qed.
Lemma program230_eval_succ M rho t:evalM M rho(σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.
Lemma program230_same_formula_correct M rho before after:
 holds M rho(program230_same_formula before after)<->
 program230_register_same M(fun i => evalM M rho(before i))(fun i => evalM M rho(after i)).
Proof.
 unfold program230_same_formula,program230_register_same.
 rewrite program230_all_formula_correct. setoid_rewrite program230_holds_equal;reflexivity.
Qed.
Lemma program230_update_formula_correct M rho before after r value:
 holds M rho(program230_update_formula before after r value)<->
 program230_register_update M r(evalM M rho value)
  (fun i => evalM M rho(before i))(fun i => evalM M rho(after i)).
Proof.
 unfold program230_update_formula,program230_register_update.
 rewrite program230_all_formula_correct. setoid_rewrite program230_holds_equal.
 split;intros H i Hi;specialize(H i Hi);destruct(Nat.eqb i r);exact H.
Qed.

Definition program230_positive_formula(Q:list bool)(before after:nat->term)r(pc':term):form:=
 ∃((before r)`[↑]==σ $0 ∧
   (pc'`[↑]==(program230_path_term(inc_path Q))`[↑] ∧
    program230_update_formula(fun i => (before i)`[↑])(fun i => (after i)`[↑])r $0)).
Theorem program230_positive_formula_correct M rho Q before after r pc':
 holds M rho(program230_positive_formula Q before after r pc')<->
 exists v,evalM M rho(before r)=succM M v /\
  evalM M rho pc'=program230_path_value M(inc_path Q) /\
  program230_register_update M r v
   (fun i => evalM M rho(before i))(fun i => evalM M rho(after i)).
Proof.
 unfold program230_positive_formula;rewrite holds_ex.
 assert(Hbody:forall v,
  holds M(v.:rho)((before r)`[↑]==σ $0 ∧
   (pc'`[↑]==(program230_path_term(inc_path Q))`[↑] ∧
    program230_update_formula(fun i => (before i)`[↑])(fun i => (after i)`[↑])r $0))<->
  evalM M rho(before r)=succM M v /\
   evalM M rho pc'=program230_path_value M(inc_path Q) /\
   program230_register_update M r v
    (fun i => evalM M rho(before i))(fun i => evalM M rho(after i))).
 { intro v.
   rewrite(holds_and M(v.:rho)((before r)`[↑]==σ $0)
     (pc'`[↑]==(program230_path_term(inc_path Q))`[↑] ∧
      program230_update_formula(fun i => (before i)`[↑])(fun i => (after i)`[↑])r $0)).
   rewrite(holds_and M(v.:rho)(pc'`[↑]==(program230_path_term(inc_path Q))`[↑])
     (program230_update_formula(fun i => (before i)`[↑])(fun i => (after i)`[↑])r $0)).
   rewrite !program230_holds_equal,program230_update_formula_correct,
     !program230_eval_up,program230_eval_succ,program230_path_term_correct.
   unfold program230_register_update. setoid_rewrite program230_eval_up;reflexivity. }
 setoid_rewrite Hbody;reflexivity.
Qed.

Definition program230_edge_step M(Q:list bool)(e:edge)(R T:nat->carrier M)pc':Prop:=
 match e with
 |EInc r=>(r<9)%nat /\pc'=program230_path_value M(inc_path Q) /\
   program230_register_update M r(succM M(R r))R T
 |EDecnz r=>(r<9)%nat /\
   ((R r=zeroM M /\pc'=program230_path_value M(brk 1 Q) /\program230_register_same M R T)\/
    exists v,R r=succM M v /\pc'=program230_path_value M(inc_path Q) /\
      program230_register_update M r v R T)
 |EBreak k=>pc'=program230_path_value M(brk k Q) /\program230_register_same M R T
 |EContinue k=>pc'=program230_path_value M(cont k Q) /\program230_register_same M R T
 |ENode _|EHalt=>False
 end.

Definition program230_edge_formula(Q:list bool)(e:edge)(before after:nat->term)(pc':term):form:=
 match e with
 |EInc r=>if Nat.ltb r 9 then
    pc'==program230_path_term(inc_path Q) ∧program230_update_formula before after r(σ(before r))
   else ⊥
 |EDecnz r=>if Nat.ltb r 9 then
    ((before r==zero ∧(pc'==program230_path_term(brk 1 Q) ∧program230_same_formula before after)) ∨
      program230_positive_formula Q before after r pc')
   else ⊥
 |EBreak k=>pc'==program230_path_term(brk k Q) ∧program230_same_formula before after
 |EContinue k=>pc'==program230_path_term(cont k Q) ∧program230_same_formula before after
 |ENode _|EHalt=>⊥
 end.

Local Opaque program230_same_formula program230_update_formula program230_all_formula program230_positive_formula.
Theorem program230_edge_formula_correct M rho Q e before after pc':
 holds M rho(program230_edge_formula Q e before after pc')<->
 program230_edge_step M Q e(fun i => evalM M rho(before i))(fun i => evalM M rho(after i))(evalM M rho pc').
Proof.
 destruct e as[n|r|r|k|k|];unfold program230_edge_formula,program230_edge_step.
 -reflexivity.
 -destruct(Nat.ltb r 9)eqn:Hr.
  +rewrite holds_and,program230_holds_equal,program230_path_term_correct,
    program230_update_formula_correct,program230_eval_succ.
   apply Nat.ltb_lt in Hr;tauto.
  +apply Nat.ltb_ge in Hr;split;[contradiction|intros[H _];lia].
 -destruct(Nat.ltb r 9)eqn:Hr.
  +rewrite holds_or.
   rewrite(holds_and M rho(before r==zero)
     (pc'==program230_path_term(brk 1 Q) ∧program230_same_formula before after)).
   rewrite(holds_and M rho(pc'==program230_path_term(brk 1 Q))
     (program230_same_formula before after)).
   rewrite !program230_holds_equal,program230_path_term_correct,
     program230_same_formula_correct,program230_positive_formula_correct.
   apply Nat.ltb_lt in Hr;tauto.
  +apply Nat.ltb_ge in Hr;split;[contradiction|intros[H _];lia].
 -rewrite holds_and,program230_holds_equal,program230_path_term_correct,program230_same_formula_correct;reflexivity.
 -rewrite holds_and,program230_holds_equal,program230_path_term_correct,program230_same_formula_correct;reflexivity.
 -reflexivity.
Qed.

Theorem program230_edge_deterministic M Q e R T U pc' pc'':
 program230_edge_step M Q e R T pc'->program230_edge_step M Q e R U pc''->
 pc'=pc'' /\forall i,(i<9)%nat->T i = U i.
Proof.
 destruct e as[n|r|r|k|k|];cbn[program230_edge_step];try contradiction.
 -intros[_[-> HT]][_[-> HU]];split;[reflexivity|]. intros i Hi.
  unfold program230_register_update in HT,HU;rewrite(HT i Hi),(HU i Hi);reflexivity.
 -intros[_ H][_ K]. destruct H as[[H0[-> HT]]|[v[Hv[-> HT]]]],
   K as[[K0[-> HU]]|[w[Hw[-> HU]]]].
  +split;[reflexivity|]. intros i Hi;rewrite(HT i Hi),(HU i Hi);reflexivity.
  +exfalso;apply(zero_ne_succ M w);congruence.
  +exfalso;apply(zero_ne_succ M v);congruence.
  +assert(E:v=w)by(apply(succ_injective M);congruence);subst w.
   split;[reflexivity|]. intros i Hi;rewrite(HT i Hi),(HU i Hi);reflexivity.
 -intros[-> HT][-> HU];split;[reflexivity|]. intros i Hi;rewrite(HT i Hi),(HU i Hi);reflexivity.
 -intros[-> HT][-> HU];split;[reflexivity|]. intros i Hi;rewrite(HT i Hi),(HU i Hi);reflexivity.
Qed.

Print Assumptions program230_edge_formula_correct.
Print Assumptions program230_edge_deterministic.
Print Assumptions p230_wf.
