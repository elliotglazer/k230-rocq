(** First-order graph, totality, uniqueness and bounds for the actual Ew
    witness request at an arbitrary model-valued carrier name. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes NumericalProofs
  SourceBounded SourceEwMonotone SourceRelativizationRules SourceRelativizationFunctionality
  SourceRelativizationBounds SourceD0Recipe.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Definition source_ew_at_formula(domain matrix z out:term):form:=∃∃∃(
  sf_formula SFMember zero(σ(lift3 z))$2 ∧
  (sr_quantifier_formula false(lift3 domain)(lift3 matrix)$1 ∧
  (sr_quantifier_formula false $2(lift3 matrix)$0 ∧sf_formula SFImpl $1 $0(lift3 out)))).
Local Opaque holds sf_formula sr_quantifier_formula.
Lemma source_ew_at_eval_succ M rho t:evalM M rho(σ t)=succM M(evalM M rho t).
Proof. reflexivity. Qed.
Theorem source_ew_at_formula_correct M rho domain matrix z out:
  holds M rho(source_ew_at_formula domain matrix z out) <->
  source_ew_at M(evalM M rho domain)(evalM M rho matrix)(evalM M rho z)(evalM M rho out).
Proof.
  unfold source_ew_at_formula,source_ew_at. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite sf_formula_correct.
  setoid_rewrite sr_quantifier_formula_correct. setoid_rewrite source_ew_at_eval_succ.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Theorem source_ew_at_total M domain matrix z:exists out,source_ew_at M domain matrix z out.
Proof.
  destruct(sf_relation_total M SFMember(zeroM M)(succM M z))as(atom&HA).
  destruct(sr_quantifier_total M false domain matrix)as(left&HL).
  destruct(sr_quantifier_total M false atom matrix)as(right&HR).
  destruct(sf_relation_total M SFImpl left right)as(out&HO).
  exists out,atom,left,right. auto.
Qed.
Theorem source_ew_at_functional M domain matrix z x y:
  source_ew_at M domain matrix z x ->source_ew_at M domain matrix z y ->x=y.
Proof.
  intros(a&l&r&HA&HL&HR&HX)(a'&l'&r'&HA'&HL'&HR'&HY).
  pose proof(sf_relation_functional M SFMember(zeroM M)(succM M z)a' a HA' HA)as E. subst a'.
  pose proof(sr_quantifier_functional M false domain matrix l' l HL' HL)as E. subst l'.
  pose proof(sr_quantifier_functional M false a matrix r' r HR' HR)as E. subst r'.
  exact(sf_relation_functional M SFImpl l r x y HX HY).
Qed.
Theorem source_ew_at_bounded M domain matrix z out k:
  source_bounded M domain(code_numeral M 1) ->source_bounded M matrix(succM M k) ->coding_lt M z k ->
  source_ew_at M domain matrix z out ->source_bounded M out k.
Proof.
  intros HD HM HZ(atom&left&right&HA&HL&HR&HO).
  pose proof(source_guarded_exists_bounded M domain matrix left k(sr_domain_bound_succ M domain k HD)HM HL)as BL.
  assert(BA:source_bounded M atom(succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M z)atom(succM M k)(or_introl eq_refl)HA)).
    split;[apply coding_zero_lt_succ|apply coding_lt_succ_cancel;exact HZ]. }
  pose proof(source_guarded_exists_bounded M atom matrix right k BA HM HR)as BR.
  exact(proj2(source_bounded_accept_binary M SFImpl left right out k(or_intror(or_intror eq_refl))HO)(conj BL BR)).
Qed.
Print Assumptions source_ew_at_formula_correct.
Print Assumptions source_ew_at_total.
Print Assumptions source_ew_at_functional.
Print Assumptions source_ew_at_bounded.
