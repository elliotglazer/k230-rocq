(** Candidate cofinality from the exact seed, proved by PA-definable
    induction over arbitrary model counters. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions NumericalProofs
 SearchStep KernelSafety RunSyntax NumericalReachability SearchTransitionTotal
 SearchProgress NumericalSearchDrain.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition numerical_candidate_progress M(seed:search_state(carrier M)) k:=
 numerical_halts_from M seed \/exists t,numerical_reaches M seed t /\
  search_pl t=zeroM M /\search_np t=addM M(search_np seed)k.
Definition candidate_progress_formula(seed:search_state term)(k:term):form:=
 halts_from_formula seed ∨∃∃∃∃∃∃
 (reach_formula(lift_state 6 seed)bound_state ∧
  (search_pl bound_state==zero ∧
   search_np bound_state==run_lift 6(search_np seed ⊕k))).
Local Opaque holds reach_formula halts_from_formula.
Lemma candidate_progress_formula_correct M rho seed k:
 holds M rho(candidate_progress_formula seed k)<->
 numerical_candidate_progress M(term_state_value M rho seed)(evalM M rho k).
Proof.
 unfold candidate_progress_formula,numerical_candidate_progress.
 rewrite holds_or,halts_from_formula_correct.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite reach_formula_correct. setoid_rewrite lift_state6_correct.
 split.
 - intros[H|[pl[np[tw[ws[dd[hh[Hr[Hp Hn]]]]]]]]];[now left|].
   right. exists(mkSearchState(carrier M)pl np tw ws dd hh). split;[exact Hr|].
   split;[exact Hp|].
   change(np=evalM M(hh .:dd .:ws .:tw .:np .:pl .:rho)
    (run_lift 6(search_np seed ⊕k)))in Hn.
   rewrite eval_run_lift6 in Hn. exact Hn.
 - intros[H|[t[Hr[Hp Hn]]]];[now left|].
   destruct t as[pl np tw ws dd hh]. right. exists pl,np,tw,ws,dd,hh.
   split;[exact Hr|]. split;[exact Hp|].
   change(np=evalM M(hh .:dd .:ws .:tw .:np .:pl .:rho)
    (run_lift 6(search_np seed ⊕k))).
   rewrite eval_run_lift6. exact Hn.
Qed.
Lemma numerical_candidate_progress_definable M(seed:search_state(carrier M)):
 Definable1 M(numerical_candidate_progress M seed).
Proof.
 destruct seed as[pl np tw ws dd hh].
 exists(candidate_progress_formula(mkSearchState term $1 $2 $3 $4 $5 $6)$0),
  (pl .:np .:tw .:ws .:dd .:hh .:(fun _=>zeroM M)).
 intro k. symmetry. rewrite candidate_progress_formula_correct. reflexivity.
Qed.

Section ReachCandidates.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Lemma candidate_add_succ x y:x+S y=S(x+y).
Proof. rewrite(Arithmetic.add_comm M x(S y)),Arithmetic.add_succ,(Arithmetic.add_comm M y x). reflexivity. Qed.
Theorem numerical_candidate_reach_from(seed:search_state D):
 search_pl seed=O->forall k,numerical_candidate_progress M seed k.
Proof.
 intro Hzero. apply(definable_induction M(numerical_candidate_progress M seed)
  (numerical_candidate_progress_definable M seed)).
 - right. exists seed. split;[apply numerical_reaches_reflexive|].
   split;[exact Hzero|]. symmetry. apply coding_add_zero_r.
 - intros k[Hhalt|[s[Hreach[Hpl Hnp]]]].
   + now left.
   + destruct(numerical_search_step_or_halt M s)as[[t Hstep]|Hhalt].
     * pose proof(proj1(numerical_step_new_candidate M s t Hpl Hstep))as Hnext.
       assert(Hreach':numerical_reaches M seed t).
       { eapply numerical_reaches_transitive;[exact Hreach|]. apply numerical_reaches_step,Hstep. }
       destruct(numerical_search_drains M t)as[Hhalt|[u[Htail[Hu Hnu]]]].
       -- left. exact(numerical_reaches_halts M seed t Hreach' Hhalt).
       -- right. exists u. split;[eapply numerical_reaches_transitive;eassumption|].
          split;[exact Hu|]. now rewrite Hnu,Hnext,Hnp,candidate_add_succ.
     * left. apply(numerical_reaches_halts M seed s Hreach),numerical_halts_immediate,Hhalt.
Qed.
Theorem numerical_candidate_reach_at_least(seed:search_state D)target:
 search_pl seed=O->~coding_lt M target(search_np seed)->
 numerical_halts_from M seed \/exists t,numerical_reaches M seed t /\
  search_pl t=O /\search_np t=target.
Proof.
 intros Hzero Hbound. destruct(coding_difference M target(search_np seed)Hbound)as[k Hk].
 destruct(numerical_candidate_reach_from seed Hzero k)as[Hhalt|[t[Hr[Hp Hn]]]].
 - now left.
 - right. exists t. split;[exact Hr|]. split;[exact Hp|]. now rewrite Hk.
Qed.
Theorem numerical_seed_reaches_candidate target:
 ~coding_lt M target(code_numeral M 3)->
 numerical_halts_from M(seed_state M) \/exists t,
  numerical_reaches M(seed_state M)t /\search_pl t=O /\search_np t=target.
Proof. intro H. exact(numerical_candidate_reach_at_least(seed_state M)target eq_refl H). Qed.
End ReachCandidates.
Print Assumptions numerical_candidate_progress_definable.
Print Assumptions numerical_candidate_reach_from.
Print Assumptions numerical_seed_reaches_candidate.
