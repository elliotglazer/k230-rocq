(** Genuine internally finite table alignment for carried ordinary files. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking BoundedCollection
 CodeExpressions NumericalProofs PowerTwoSyntax TM230RegisterWords TM230CarryPrefixes TM230ReturnPrefixes TM230IncrementAlignment.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
Definition machine230_inserted_prefix_value M x:=addM M(code_numeral M 1)(mulM M(code_numeral M 2)x).
Definition machine230_inserted_prefix_relation M lb lc i out:=exists x,
 beta M lb lc i x /\out=machine230_inserted_prefix_value M x.
Definition machine230_inserted_prefix_relation_formula:form:=∃
 (beta_formula $3 $4 $2 $0 ∧$1==num 1⊕num 2⊗$0).
Local Opaque holds beta_formula.
Lemma machine230_inserted_prefix_relation_correct M rho lb lc i out:
 holds M(out.:i.:lb.:lc.:rho)machine230_inserted_prefix_relation_formula <->
 machine230_inserted_prefix_relation M lb lc i out.
Proof.
 unfold machine230_inserted_prefix_relation_formula,machine230_inserted_prefix_relation,machine230_inserted_prefix_value.
 rewrite holds_ex. setoid_rewrite holds_and. setoid_rewrite beta_formula_correct.
 setoid_rewrite power_holds_equal. setoid_rewrite register_eval_add.
 setoid_rewrite register_eval_mul. setoid_rewrite code_eval_num. reflexivity.
Qed.
Theorem machine230_inserted_prefix_table M lb lc count:exists rb rc,
 forall i x,coding_lt M i count ->beta M lb lc i x ->
 beta M rb rc i(machine230_inserted_prefix_value M x).
Proof.
 set(theta:=machine230_inserted_prefix_relation_formula).
 set(rho:=lb.:lc.:(fun _=>zeroM M)).
 assert(HT:forall i,coding_lt M i count ->exists r,holds M(r.:i.:rho)theta).
 {intros i Hi. destruct(beta_total M lb lc i)as[x Hx].
  exists(machine230_inserted_prefix_value M x). apply machine230_inserted_prefix_relation_correct.
  exists x;auto. }
 assert(HU:forall i r s,coding_lt M i count ->holds M(r.:i.:rho)theta ->holds M(s.:i.:rho)theta ->r=s).
 {intros i r s Hi Hr Hs. apply machine230_inserted_prefix_relation_correct in Hr,Hs.
  destruct Hr as[x[Hx Er]],Hs as[y[Hy Es]].
  assert(E:x=y)by(eapply beta_unique;eassumption). congruence. }
 destruct(bounded_collection M theta rho count HT)as[bound HB].
 assert(HB':forall i r,coding_lt M i count ->holds M(r.:i.:rho)theta ->coding_lt M r(succM M bound)).
 {intros i r Hi Hr. destruct(HB i Hi)as[w[Hw HF]].
  assert(E:r=w)by(exact(HU i r w Hi Hr HF)). subst r.
  exact(coding_lt_trans M w bound(succM M bound)Hw(coding_lt_succ M bound)). }
 destruct(beta_pack_function M rho theta count bound HT HB' HU)as[rb[rc HP]].
 exists rb,rc. intros i x Hi Hx. apply(proj2(HP i(machine230_inserted_prefix_value M x)Hi)).
 apply machine230_inserted_prefix_relation_correct. exists x;auto.
Qed.
Theorem machine230_carry_to_return_prefixes M vb vc lb lc count:
 machine230_carry_prefix_chain M vb vc lb lc count ->
 exists rb rc,
 (forall i x,coding_lt M i(succM M count)->beta M lb lc i x ->
 beta M rb rc i(machine230_inserted_prefix_value M x)) /\
 machine230_return_prefix_chain M vb vc rb rc count.
Proof.
 intro HL. destruct(machine230_inserted_prefix_table M lb lc(succM M count))as[rb[rc HP]].
 exists rb,rc. split;[exact HP|]. intros i Hi.
 destruct(HL i Hi)as[v[x[y[Hv[Hx[Hy Hstep]]]]]].
 exists v,(machine230_inserted_prefix_value M x),(machine230_inserted_prefix_value M y).
 split;[exact Hv|]. split.
 -apply HP;[apply coding_lt_succ_cases;now left|exact Hx].
 -split;[apply HP;[now apply coding_lt_succ_cancel|exact Hy]|].
  exact(machine230_carry_inserted_one M v x y Hstep).
Qed.
Theorem machine230_carry_to_return_endpoints M vb vc lb lc count first last:
 machine230_carry_prefix_chain M vb vc lb lc count ->
 beta M lb lc(zeroM M)first ->beta M lb lc count last ->
 exists rb rc,machine230_return_prefix_chain M vb vc rb rc count /\
 beta M rb rc(zeroM M)(machine230_inserted_prefix_value M first) /\
 beta M rb rc count(machine230_inserted_prefix_value M last).
Proof.
 intros HL HF HE. destruct(machine230_carry_to_return_prefixes M vb vc lb lc count HL)as[rb[rc[HP HR]]].
 exists rb,rc. split;[exact HR|]. split.
 -exact(HP _ _ (coding_zero_lt_succ M count)HF).
 -exact(HP _ _ (coding_lt_succ M count)HE).
Qed.
Print Assumptions machine230_inserted_prefix_table.
Print Assumptions machine230_carry_to_return_prefixes.
Print Assumptions machine230_carry_to_return_endpoints.
