(** Actual internally coded arithmetic prefixes of a carried register list. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions NumericalProofs
 PowerTwoSyntax PowerTwoRecurrence PowerTwoPositive TM230RegisterWords.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Definition machine230_carry_prefix_step M v left out:=exists p k,power2 M v p /\
 p=succM M k /\out=addM M(mulM M p(addM M(mulM M(code_numeral M 4)left)(code_numeral M 2)))k.
Definition machine230_carry_prefix_step_formula(v left out:term):form:=∃∃
 (power2_formula(code_lift2 v)$1 ∧($1==σ $0 ∧
 code_lift2 out==$1⊗(num 4⊗code_lift2 left⊕num 2)⊕$0)).
Definition machine230_carry_prefix_chain M vb vc lb lc count:=forall i,coding_lt M i count->
 exists v left out,beta M vb vc i v /\beta M lb lc i left /\
 beta M lb lc(succM M i)out /\machine230_carry_prefix_step M v left out.
Definition machine230_carry_prefix_chain_formula(vb vc lb lc count:term):form:=∀
 (Peano.sless $0 count`[↑]→∃∃∃
 (beta_formula(code_lift4 vb)(code_lift4 vc)$3 $2 ∧
 (beta_formula(code_lift4 lb)(code_lift4 lc)$3 $1 ∧
 (beta_formula(code_lift4 lb)(code_lift4 lc)(σ $3)$0 ∧
 machine230_carry_prefix_step_formula $2 $1 $0)))).
Definition machine230_carry_prefix_total_at M vb vc left count:=exists lb lc,
 beta M lb lc(zeroM M)left /\machine230_carry_prefix_chain M vb vc lb lc count.
Local Opaque holds Peano.sless beta_formula power2_formula.
Lemma machine230_carry_prefix_step_formula_correct M rho v left out:
 holds M rho(machine230_carry_prefix_step_formula v left out)<->
 machine230_carry_prefix_step M(evalM M rho v)(evalM M rho left)(evalM M rho out).
Proof.
 unfold machine230_carry_prefix_step_formula,machine230_carry_prefix_step.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite power2_formula_correct. setoid_rewrite power_holds_equal.
 repeat setoid_rewrite register_eval_succ. repeat setoid_rewrite register_eval_add.
 repeat setoid_rewrite register_eval_mul. repeat setoid_rewrite code_eval_num.
 repeat setoid_rewrite code_eval_lift2.
 repeat first[progress(setoid_rewrite register_eval_add)|progress(setoid_rewrite register_eval_mul)|progress(setoid_rewrite code_eval_num)|progress(setoid_rewrite code_eval_lift2)]. reflexivity.
Qed.
Lemma machine230_carry_prefix_chain_formula_correct M rho vb vc lb lc count:
 holds M rho(machine230_carry_prefix_chain_formula vb vc lb lc count)<->
 machine230_carry_prefix_chain M(evalM M rho vb)(evalM M rho vc)(evalM M rho lb)(evalM M rho lc)(evalM M rho count).
Proof.
 unfold machine230_carry_prefix_chain_formula,machine230_carry_prefix_chain.
 rewrite holds_all. setoid_rewrite holds_imp. repeat setoid_rewrite holds_ex.
 repeat setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite machine230_carry_prefix_step_formula_correct. setoid_rewrite less_formula_correct.
 repeat setoid_rewrite code_eval_lift4. setoid_rewrite register_eval_up. reflexivity.
Qed.
Lemma machine230_carry_prefix_total_definable M vb vc left:
 Definable1 M(machine230_carry_prefix_total_at M vb vc left).
Proof.
 exists(∃∃(beta_formula $1 $0 zero $5 ∧machine230_carry_prefix_chain_formula $3 $4 $1 $0 $2)),
 (vb.:vc.:left.:(fun _=>zeroM M)). intro count.
 unfold machine230_carry_prefix_total_at. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
 setoid_rewrite beta_formula_correct. setoid_rewrite machine230_carry_prefix_chain_formula_correct. reflexivity.
Qed.
Lemma machine230_carry_prefix_step_total M v left:exists out,machine230_carry_prefix_step M v left out.
Proof.
 destruct(power2_total M v)as[p Hp]. destruct(power2_positive_successor M v p Hp)as[k Hk].
 exists(addM M(mulM M p(addM M(mulM M(code_numeral M 4)left)(code_numeral M 2)))k),p,k. auto.
Qed.
Theorem machine230_carry_prefix_total M vb vc left:forall count,
 machine230_carry_prefix_total_at M vb vc left count.
Proof.
 apply(definable_induction M(machine230_carry_prefix_total_at M vb vc left)
 (machine230_carry_prefix_total_definable M vb vc left)).
 - destruct(beta_extension M(zeroM M)(zeroM M)(zeroM M)left)as[lb[lc[HP H0]]].
   exists lb,lc. split;[exact H0|]. intros i Hi. exfalso;exact(coding_not_lt_zero M i Hi).
 - intros n[lb[lc[H0 HC]]]. destruct(beta_total M vb vc n)as[v Hv].
   destruct(beta_total M lb lc n)as[x Hx].
   destruct(machine230_carry_prefix_step_total M v x)as[y Hy].
   destruct(beta_extension M lb lc(succM M n)y)as[db[dc[HP Hlast]]].
   exists db,dc. split;[exact(HP _ _ (coding_zero_lt_succ M n)H0)|].
   intros i Hi. destruct(proj1(coding_lt_succ_cases M i n)Hi)as[Hin|Ei].
   + destruct(HC i Hin)as[vi[xi[yi[Hvi[Hxi[Hyi Hstep]]]]]].
     exists vi,xi,yi. split;[exact Hvi|]. split;[exact(HP i xi Hi Hxi)|].
     split;[|exact Hstep]. apply HP;[now apply coding_lt_succ_cancel|exact Hyi].
   + subst i. exists v,x,y. split;[exact Hv|]. split;[exact(HP _ _ (coding_lt_succ M n)Hx)|]. auto.
Qed.
Print Assumptions machine230_carry_prefix_chain_formula_correct.
Print Assumptions machine230_carry_prefix_total.
