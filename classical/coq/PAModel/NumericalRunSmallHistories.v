(** Initial and one-step numerical histories. The external list helper
    packs only the fixed six-register record, never an internal run length. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
 CodeExpressions NumericalProofs SearchStep RunSyntax NumericalRunConcatenation.
From Stdlib Require Import Lists.List Lia setoid_ring.Ring.
Unset Implicit Arguments.
Section SmallHistories.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation six := (code_numeral M 6).
Add Ring small_history_ring : (model_semiring M).
Lemma run_numeral_lt n m:(n<m)%nat->coding_lt M(code_numeral M n)(code_numeral M m).
Proof.
 revert n. induction m as[|m IH];intros n H;[lia|].
 destruct n;cbn[code_numeral].
 - apply coding_zero_lt_succ.
 - apply coding_lt_succ_cancel,IH. lia.
Qed.
Lemma run_fixed_fields_pack (values:list D):
 exists b c,forall j v,nth_error values j=Some v->beta M b c(code_numeral M j)v.
Proof.
 induction values as[|a values [b[c IH]]].
 - exists Z,Z. intros j v H. destruct j;discriminate.
 - destruct(beta_concatenate M a a(S Z)b c(code_numeral M(length values)))as[d[e[HL HR]]].
   exists d,e. intros j v H. destruct j as[|j].
   + cbn in H. inversion H;subst v. apply HL;[apply coding_zero_lt_succ|apply beta_singleton].
   + cbn in H. pose proof(IH j v H)as Hv.
     assert(Hj:(j<length values)%nat).
     { apply nth_error_Some. rewrite H. discriminate. }
     pose proof(HR(code_numeral M j)v(run_numeral_lt j(length values)Hj)Hv)as P.
     cbn[code_numeral]. rewrite(Arithmetic.add_succ M Z(code_numeral M j)),coding_add_zero in P.
     exact P.
Qed.
Lemma run_state_index_zero j:state_index M Z j=code_numeral M j.
Proof. unfold state_index. ring. Qed.
Theorem numerical_state_at_zero_total (s:search_state D):exists b c,state_at M b c Z s.
Proof.
 destruct s as[pl np tw ws dd hh].
 destruct(run_fixed_fields_pack(pl::np::tw::ws::dd::hh::nil))as[b[c H]].
 exists b,c. change(beta M b c(state_index M Z 0)pl /\
 (beta M b c(state_index M Z 1)np /\(beta M b c(state_index M Z 2)tw /\
 (beta M b c(state_index M Z 3)ws /\(beta M b c(state_index M Z 4)dd /\
 beta M b c(state_index M Z 5)hh))))).
 rewrite !run_state_index_zero.
 exact(conj(H 0 pl eq_refl)(conj(H 1 np eq_refl)(conj(H 2 tw eq_refl)
  (conj(H 3 ws eq_refl)(conj(H 4 dd eq_refl)(H 5 hh eq_refl)))))).
Qed.
Theorem numerical_run_from_zero (s:search_state D):
 exists b c,numerical_run_from M b c Z s /\state_at M b c Z s.
Proof.
 destruct(numerical_state_at_zero_total s)as[b[c H]]. exists b,c.
 split;[split;[exact H|]|exact H].
 intros i s0 t Hi. exfalso. exact(coding_not_lt_zero M i Hi).
Qed.
Theorem numerical_run_from_one (s t:search_state D):enumerator_step M s t->
 exists b c,numerical_run_from M b c(S Z)s /\state_at M b c(S Z)t.
Proof.
 intro Hstep. destruct(numerical_state_at_zero_total s)as[b[c HS]].
 destruct(numerical_state_at_zero_total t)as[d[e HT]].
 destruct(beta_concatenate M b c six d e six)as[f[g[HL HR]]].
 assert(HS':state_at M f g Z s).
 { assert(HL':forall k v,coding_lt M k(six*(S Z))->beta M b c k v->beta M f g(six*Z+k)v).
   { intros k v HK HV. replace(six*Z+k)with k by ring.
     apply HL;[replace(six*(S Z))with six in HK by ring;exact HK|exact HV]. }
   pose proof(run_state_at_transport M b c f g Z(S Z)HL' Z s(coding_zero_lt_succ M Z)HS)as P.
   now rewrite coding_add_zero in P. }
 assert(HT':state_at M f g(S Z)t).
 { assert(HR':forall k v,coding_lt M k(six*(S Z))->beta M d e k v->beta M f g(six*(S Z)+k)v).
   { intros k v HK HV. replace(six*(S Z))with six in * by ring. exact(HR k v HK HV). }
   pose proof(run_state_at_transport M d e f g(S Z)(S Z)HR' Z t(coding_zero_lt_succ M Z)HT)as P.
   now rewrite coding_add_zero_r in P. }
 exists f,g. split;[split;[exact HS'|]|exact HT'].
 intros i u v Hi Hu Hv. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi|E].
 - exfalso. exact(coding_not_lt_zero M i Hi).
 - subst i. pose proof(state_at_functional M f g Z u s Hu HS')as Eu.
   pose proof(state_at_functional M f g(S Z)v t Hv HT')as Ev. now subst u v.
Qed.
Theorem numerical_run_from_extend b c N s0 s t:
 numerical_run_from M b c N s0->state_at M b c N s->enumerator_step M s t->
 exists f g,numerical_run_from M f g(S N)s0 /\state_at M f g(S N)t /\
 (forall i u,coding_lt M i(S N)->(state_at M b c i u<->state_at M f g i u)).
Proof.
 intros Hrun HS Hstep. destruct(numerical_run_from_one s t Hstep)as[d[e[Hone HT]]].
 destruct(numerical_run_from_join M b c N d e(S Z)s0 s Hrun HS Hone)as[f[g[Hjoined[HL HR]]]].
 assert(E:N+S Z=S N)by(symmetry;apply succ_as_add).
 exists f,g. split;[now rewrite <-E|]. split;[|exact HL]. rewrite <-E.
 apply(HR(S Z)t(coding_lt_succ M(S Z))). exact HT.
Qed.
End SmallHistories.
Print Assumptions numerical_state_at_zero_total.
Print Assumptions numerical_run_from_zero.
Print Assumptions numerical_run_from_one.
Print Assumptions numerical_run_from_extend.
