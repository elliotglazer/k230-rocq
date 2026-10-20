(** The actual first-candidate AX reset, before entering a compiled block.
    Candidate codes have no outer successor; the running-program codes do. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
 CodeExpressions CodeDescent SearchStep KernelSafety RunSyntax NumericalReachability
 NumericalSearchDrain NumericalCandidateReachability.
Unset Implicit Arguments.

Definition reset_candidate M tail candidate : Prop :=
 exists p0 p1 p2,
 pair_graph M (zeroM M) tail p0 /\
 pair_graph M (code_numeral M 1) p0 p1 /\
 pair_graph M (code_numeral M 1) p1 p2 /\
 pair_graph M (code_numeral M 3) p2 candidate.

Lemma reset_candidate_total M tail : exists candidate,reset_candidate M tail candidate.
Proof.
 destruct(pair_total M (zeroM M)tail)as[p0 H0].
 destruct(pair_total M (code_numeral M 1)p0)as[p1 H1].
 destruct(pair_total M (code_numeral M 1)p1)as[p2 H2].
 destruct(pair_total M (code_numeral M 3)p2)as[p H3].
 exists p,p0,p1,p2. auto.
Qed.
Lemma reset_candidate_after_seed M tail candidate : reset_candidate M tail candidate ->
 ~coding_lt M candidate(code_numeral M 3).
Proof.
 intros[p0[p1[p2[H0[H1[H2 H3]]]]]].
 destruct(proj1(pair_coordinate_bounds M _ _ _ H3))as[d Hd].
 assert(E:candidate=succM M(succM M(succM M d))).
 { rewrite Hd. change(addM M(succM M(succM M(succM M(zeroM M))))d=succM M(succM M(succM M d))).
   now rewrite !Arithmetic.add_succ,Arithmetic.add_zero. }
 rewrite E. change(~coding_lt M (succM M(succM M(succM M d)))
   (succM M(succM M(succM M(zeroM M))))).
 rewrite !coding_lt_succ_cancel. apply coding_not_lt_zero.
Qed.

Lemma numerical_reset_candidate_step M tail candidate (s:search_state(carrier M)):
 reset_candidate M tail candidate ->search_pl s=zeroM M ->search_np s=candidate ->
 exists t w,enumerator_step M s
  (mkSearchState(carrier M)tail(succM M candidate)t w(zeroM M)(zeroM M)).
Proof.
 intros[p0[p1[p2[H0[H1[H2 H3]]]]]] Hpl Hnp.
 destruct s as[pl np tw ws d h]. cbn in Hpl,Hnp;subst pl np.
 set(d1:=addM M d(code_numeral M 1)).
 set(b:=addM M h(code_numeral M 1)).
 destruct(code_relation_total M (E_ax_stack(CEvar 0)(CEvar 1)(CEvar 2)
  (CEvar 3)(CEvar 4)(CEvar 5)(CEvar 6))
  (search_values M(d1::h::b::zeroM M::zeroM M::tw::ws::nil)))as[w Hw].
 destruct(code_relation_total M(E_bundle(CEvar 0)(CEvar 1)(CEvar 2))
  (search_values M(d1::b::zeroM M::nil)))as[t Ht].
 exists t,w. exists candidate,(succM M candidate),(code_numeral M 3),p2,
  (code_numeral M 1),p1,d1. split.
 - split.
   + left. split;[reflexivity|]. split;[reflexivity|].
     apply search_add_graph_correct. apply succ_as_add.
   + split;[now apply search_pair_graph_correct|].
     split;[now apply search_pair_graph_correct|].
     apply search_add_graph_correct;reflexivity.
 - right;right;right. exists(zeroM M),(code_numeral M 1),p0,
    (zeroM M),tail,b.
   split;[apply search_add_graph_correct;symmetry;apply coding_add_zero|].
   split;[now apply search_pair_graph_correct|].
   split;[now apply search_pair_graph_correct|].
   split;[apply search_add_graph_correct;reflexivity|].
   split;[reflexivity|]. split;[reflexivity|].
   split;[reflexivity|]. split;[reflexivity|]. split;[exact Hw|].
   right. split.
   + unfold d1. change(zeroM M<>addM M d(succM M(zeroM M))).
     rewrite <-succ_as_add. apply zero_ne_succ.
   + split.
     * unfold b. change(zeroM M<>addM M h(succM M(zeroM M))).
       rewrite <-succ_as_add. apply zero_ne_succ.
     * exact Ht.
Qed.

Theorem numerical_seed_enters_program M tail :
 numerical_halts_from M(seed_state M) \/
 exists candidate t w,reset_candidate M tail candidate /\
  numerical_reaches M(seed_state M)
   (mkSearchState(carrier M)tail(succM M candidate)t w(zeroM M)(zeroM M)).
Proof.
 destruct(reset_candidate_total M tail)as[c Hc].
 destruct(numerical_seed_reaches_candidate M c(reset_candidate_after_seed M tail c Hc))
  as[Hhalt|[s[Hr[Hpl Hnp]]]];[now left|].
 destruct(numerical_reset_candidate_step M tail c s Hc Hpl Hnp)as[t[w Hstep]].
 right. exists c,t,w. split;[exact Hc|].
 eapply numerical_reaches_transitive;[exact Hr|].
 apply numerical_reaches_step,Hstep.
Qed.

Print Assumptions reset_candidate_after_seed.
Print Assumptions numerical_reset_candidate_step.
Print Assumptions numerical_seed_enters_program.
