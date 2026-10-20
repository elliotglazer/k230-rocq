(** Reachability algebra and draining proved with internally finite histories. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CourseOfValues
  SearchStep RunSyntax SearchTransitionTotal SearchProgress NumericalReachability
  NumericalRunConcatenation NumericalRunSmallHistories.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Section Reachability.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Definition PA := fun ax H rho=>axioms M ax rho H.

Lemma numerical_reaches_reflexive s:numerical_reaches M s s.
Proof.
  destruct(numerical_run_from_zero M s)as[b[c[Hr Hs]]]. exists b,c,O;auto.
Qed.
Lemma numerical_reaches_step s t:enumerator_step M s t->numerical_reaches M s t.
Proof.
  intro H;destruct(numerical_run_from_one M s t H)as[b[c[Hr Ht]]]. exists b,c,(S O);auto.
Qed.
Lemma numerical_reaches_transitive s t u:
  numerical_reaches M s t->numerical_reaches M t u->numerical_reaches M s u.
Proof.
  intros[b[c[n[Hr Ht]]]][d[e[k[Hs Hu]]]].
  destruct(numerical_run_from_join M b c n d e k s t Hr Ht Hs)as[f[g[Hfg[_ HR]]]].
  exists f,g,(addM M n k). split;[exact Hfg|].
  exact(proj1(HR k u(coding_lt_succ M k))Hu).
Qed.
Lemma numerical_halts_immediate s:enumerator_halt M s->numerical_halts_from M s.
Proof.
  intro H;destruct(numerical_run_from_zero M s)as[b[c[Hr Hs]]]. exists b,c,O.
  split;[exact Hr|]. exists s;auto.
Qed.
Lemma numerical_reaches_halts s t:
  numerical_reaches M s t->numerical_halts_from M t->numerical_halts_from M s.
Proof.
  intros[b[c[n[Hr Ht]]]][d[e[k[Hs[u[Hu Hhalt]]]]]].
  destruct(numerical_run_from_join M b c n d e k s t Hr Ht Hs)as[f[g[Hfg[_ HR]]]].
  exists f,g,(addM M n k). split;[exact Hfg|]. exists u;split;[|exact Hhalt].
  exact(proj1(HR k u(coding_lt_succ M k))Hu).
Qed.

Theorem numerical_search_drains initial:numerical_drains M initial.
Proof.
  assert(H:forall k,forall s,search_pl s=k->numerical_drains M s).
  { apply(definable_strong_induction M
      (fun k=>forall s,search_pl s=k->numerical_drains M s)
      (numerical_drains_definable M)).
    intros k IH s Hpl.
    destruct(@Peano.zero_or_succ D(raw_interpretation M)PA k)as[Hz|[p Hp]].
    - right. exists s. split;[apply numerical_reaches_reflexive|]. split;[now rewrite Hpl,Hz|reflexivity].
    - destruct(numerical_search_step_or_halt M s)as[[t Hstep]|Hhalt].
      + destruct(numerical_step_positive_decreases M s t p)as[Hlt Hnp];[now rewrite Hpl,Hp|exact Hstep|].
        rewrite Hpl in Hlt.
        specialize(IH(search_pl t)Hlt t eq_refl).
        destruct IH as[Hhalt|[u[Hreach[Hu Hnpu]]]].
        * left. eapply numerical_reaches_halts;[apply numerical_reaches_step;exact Hstep|exact Hhalt].
        * right. exists u. split;[eapply numerical_reaches_transitive;[apply numerical_reaches_step;exact Hstep|exact Hreach]|].
          split;[exact Hu|congruence].
      + left. apply numerical_halts_immediate;exact Hhalt. }
  exact(H(search_pl initial)initial eq_refl).
Qed.
End Reachability.

Print Assumptions numerical_reaches_transitive.
Print Assumptions numerical_search_drains.





