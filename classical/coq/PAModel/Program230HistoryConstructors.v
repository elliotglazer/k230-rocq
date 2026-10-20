(** Initial and one-step numerical histories. The external list helper
    packs only the fixed ten-register record, never an internal run length. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking
 CodeExpressions NumericalProofs Program230Configurations Program230Histories Program230HistoryJoin.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Lia setoid_ring.Ring.
Unset Implicit Arguments.
Section SmallHistories.
Variable M:Model.
Variable step:form.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation ten := (code_numeral M 10).
Add Ring small_history_ring : (model_semiring M).
Lemma program230_numeral_lt n m:(n<m)%nat->coding_lt M(code_numeral M n)(code_numeral M m).
Proof.
 revert n. induction m as[|m IH];intros n H;[lia|].
 destruct n;cbn[code_numeral].
 - apply coding_zero_lt_succ.
 - apply coding_lt_succ_cancel,IH. lia.
Qed.
Lemma program230_fixed_fields_pack (values:list D):
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
     pose proof(HR(code_numeral M j)v(program230_numeral_lt j(length values)Hj)Hv)as P.
     cbn[code_numeral]. rewrite(Arithmetic.add_succ M Z(code_numeral M j)),coding_add_zero in P.
     exact P.
Qed.
Lemma program230_field_index_zero j:program230_field_index M Z j=code_numeral M j.
Proof. unfold program230_field_index. ring. Qed.
Theorem program230_state_at_zero_total (s:program230_configuration D):exists b c,program230_state_at M b c Z s.
Proof.
 destruct s as[p a0 a1 a2 a3 a4 a5 a6 a7 a8].
 destruct(program230_fixed_fields_pack(p::a0::a1::a2::a3::a4::a5::a6::a7::a8::nil))as[b[c H]].
 exists b,c. intros j Hj. rewrite program230_field_index_zero.
 destruct j as[|j];[exact(H 0 p eq_refl)|].
 destruct j as[|j];[exact(H 1 a0 eq_refl)|].
 destruct j as[|j];[exact(H 2 a1 eq_refl)|].
 destruct j as[|j];[exact(H 3 a2 eq_refl)|].
 destruct j as[|j];[exact(H 4 a3 eq_refl)|].
 destruct j as[|j];[exact(H 5 a4 eq_refl)|].
 destruct j as[|j];[exact(H 6 a5 eq_refl)|].
 destruct j as[|j];[exact(H 7 a6 eq_refl)|].
 destruct j as[|j];[exact(H 8 a7 eq_refl)|].
 destruct j as[|j];[exact(H 9 a8 eq_refl)|].
 lia.
Qed.
Theorem program230_history_zero (s:program230_configuration D):
 exists b c,program230_history M step b c Z s /\program230_state_at M b c Z s.
Proof.
 destruct(program230_state_at_zero_total s)as[b[c H]]. exists b,c.
 split;[split;[exact H|]|exact H].
 intros i s0 t Hi. exfalso. exact(coding_not_lt_zero M i Hi).
Qed.
Theorem program230_history_one (s t:program230_configuration D):program230_step M step s t->
 exists b c,program230_history M step b c(S Z)s /\program230_state_at M b c(S Z)t.
Proof.
 intro Hstep. destruct(program230_state_at_zero_total s)as[b[c HS]].
 destruct(program230_state_at_zero_total t)as[d[e HT]].
 destruct(beta_concatenate M b c ten d e ten)as[f[g[HL HR]]].
 assert(HS':program230_state_at M f g Z s).
 { assert(HL':forall k v,coding_lt M k(ten*(S Z))->beta M b c k v->beta M f g(ten*Z+k)v).
   { intros k v HK HV. replace(ten*Z+k)with k by ring.
     apply HL;[replace(ten*(S Z))with ten in HK by ring;exact HK|exact HV]. }
   pose proof(program230_state_at_transport M b c f g Z(S Z)HL' Z s(coding_zero_lt_succ M Z)HS)as P.
   now rewrite coding_add_zero in P. }
 assert(HT':program230_state_at M f g(S Z)t).
 { assert(HR':forall k v,coding_lt M k(ten*(S Z))->beta M d e k v->beta M f g(ten*(S Z)+k)v).
   { intros k v HK HV. replace(ten*(S Z))with ten in * by ring. exact(HR k v HK HV). }
   pose proof(program230_state_at_transport M d e f g(S Z)(S Z)HR' Z t(coding_zero_lt_succ M Z)HT)as P.
   now rewrite coding_add_zero_r in P. }
 exists f,g. split;[split;[exact HS'|]|exact HT'].
 intros i u v Hi Hu Hv. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi|E].
 - exfalso. exact(coding_not_lt_zero M i Hi).
 - subst i. pose proof(program230_state_at_functional M f g Z u s Hu HS')as Eu.
   pose proof(program230_state_at_functional M f g(S Z)v t Hv HT')as Ev. now subst u v.
Qed.
Theorem program230_history_extend b c N s0 s t:
 program230_history M step b c N s0->program230_state_at M b c N s->program230_step M step s t->
 exists f g,program230_history M step f g(S N)s0 /\program230_state_at M f g(S N)t /\
 (forall i u,coding_lt M i(S N)->(program230_state_at M b c i u<->program230_state_at M f g i u)).
Proof.
 intros Hrun HS Hstep. destruct(program230_history_one s t Hstep)as[d[e[Hone HT]]].
 destruct(program230_history_join M step b c N d e(S Z)s0 s Hrun HS Hone)as[f[g[Hjoined[HL HR]]]].
 assert(E:N+S Z=S N)by(symmetry;apply succ_as_add).
 exists f,g. split;[now rewrite <-E|]. split;[|exact HL]. rewrite <-E.
 apply(HR(S Z)t(coding_lt_succ M(S Z))). exact HT.
Qed.
End SmallHistories.
Print Assumptions program230_state_at_zero_total.
Print Assumptions program230_history_zero.
Print Assumptions program230_history_one.
Print Assumptions program230_history_extend.
