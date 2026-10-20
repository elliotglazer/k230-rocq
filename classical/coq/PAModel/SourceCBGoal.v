(** Canonical bounded-parameter witness collection. The Dn roles are
    ordinal0, container1, remaining parameters2+. The existential goal
    has container0 and remaining parameters1+. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded SourceD0Recipe SourceDn SourceDnBounds SourceQfFunctionality
  SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_cb_goal M domain level ordinal count phi out :=exists d0 dn body,
  source_d0_recipe M domain level phi d0 /\source_dn M count d0 dn /\
  sf_relation M SFAnd ordinal dn body /\sf_relation M SFEx body(zeroM M)out.
Definition cb_lift3(t:term):term:=t`[↑]`[↑]`[↑].
Definition source_cb_goal_formula(domain level ordinal count phi out:term):form:=
  ∃∃∃(source_d0_recipe_formula(cb_lift3 domain)(cb_lift3 level)(cb_lift3 phi)$2 ∧
    (source_dn_formula(cb_lift3 count)$2 $1 ∧
    (sf_formula SFAnd(cb_lift3 ordinal)$1 $0 ∧sf_formula SFEx $0 zero(cb_lift3 out)))).
Local Opaque holds source_d0_recipe_formula source_dn_formula sf_formula.

Lemma cb_eval_lift3 M rho a b c t:evalM M(a.:b.:c.:rho)(cb_lift3 t)=evalM M rho t.
Proof. unfold cb_lift3,evalM. now rewrite !eval_up. Qed.

Theorem source_cb_goal_formula_correct M rho domain level ordinal count phi out:
  holds M rho(source_cb_goal_formula domain level ordinal count phi out) <->
  source_cb_goal M(evalM M rho domain)(evalM M rho level)(evalM M rho ordinal)
    (evalM M rho count)(evalM M rho phi)(evalM M rho out).
Proof.
  unfold source_cb_goal_formula,source_cb_goal.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_d0_recipe_formula_correct. setoid_rewrite source_dn_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite cb_eval_lift3. reflexivity.
Qed.

Theorem source_cb_goal_total M domain level ordinal count phi:
  exists out,source_cb_goal M domain level ordinal count phi out.
Proof.
  destruct(source_d0_recipe_total M domain level phi) as(d0&HD0).
  destruct(source_dn_total M count d0) as(dn&HDN).
  destruct(sf_relation_total M SFAnd ordinal dn) as(body&HBody).
  destruct(sf_relation_total M SFEx body(zeroM M)) as(out&HOut).
  exists out,d0,dn,body. repeat split;assumption.
Qed.

Theorem source_cb_goal_functional M domain level ordinal count phi f g:
  source_cb_goal M domain level ordinal count phi f ->source_cb_goal M domain level ordinal count phi g ->f=g.
Proof.
  intros(d0&dn&body&HD0&HDN&HBody&HF)(d0'&dn'&body'&HD0'&HDN'&HBody'&HG).
  pose proof(source_d0_recipe_functional M domain level phi d0 d0' HD0 HD0') as E. subst d0'.
  pose proof(source_dn_functional M count d0 dn dn' HDN HDN') as E. subst dn'.
  pose proof(sf_relation_functional M SFAnd ordinal dn body body' HBody HBody') as E. subst body'.
  exact(sf_relation_functional M SFEx body(zeroM M)f g HF HG).
Qed.

Theorem source_cb_goal_bounded M domain level ordinal count phi out n:
  source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->
  source_bounded M ordinal(code_numeral M 1) ->source_bounded M phi(addM M count(succM M n)) ->
  source_cb_goal M domain level ordinal count phi out ->source_bounded M out(succM M n).
Proof.
  intros HD HL HO HB(d0&dn&body&HD0&HDN&HBody&HEx).
  assert(HB':source_bounded M phi(succM M(addM M count n))).
  { rewrite Arithmetic.add_comm,Arithmetic.add_succ,Arithmetic.add_comm in HB. exact HB. }
  pose proof(source_d0_recipe_bounded M domain level phi d0(addM M count n)HD HL HB' HD0) as HD0B.
  assert(HD0B':source_bounded M d0(addM M count(succM M(succM M n)))).
  { rewrite Arithmetic.add_comm,!Arithmetic.add_succ,Arithmetic.add_comm. exact HD0B. }
  pose proof(source_dn_bounded M count d0 dn n HDN HD0B') as HDNB.
  apply(proj2(source_bounded_accept_unary M SFEx body out(succM M n)(or_intror eq_refl)HEx)).
  apply(proj2(source_bounded_accept_binary M SFAnd ordinal dn body(succM M(succM M n))
    (or_introl eq_refl)HBody)). split;[|exact HDNB].
  exact(sr_domain_bound_succ M ordinal(succM M n)HO).
Qed.

Print Assumptions source_cb_goal_formula_correct.
Print Assumptions source_cb_goal_total.
Print Assumptions source_cb_goal_functional.
Print Assumptions source_cb_goal_bounded.
