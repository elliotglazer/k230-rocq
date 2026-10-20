(** Syntax rules for genuine relativization to a variable-coded set. The
    carrier name rises under each source quantifier; its guard there is
    variable0 membership in the raised carrier. These are syntax rules only. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  NumericalTraces SentenceBounds SourceRelativizationRules NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition ssr_quantifier M (universal:bool) name w v :=exists guard mid,
  sf_relation M SFMember (zeroM M)(succM M name) guard /\
  sf_relation M (if universal then SFImpl else SFAnd) guard w mid /\
  sf_relation M (if universal then SFAll else SFEx) mid (zeroM M) v.
Definition ssr_quantifier_formula (universal:bool)(name w v:term) :form :=
  ∃∃(sf_formula SFMember zero (σ(code_lift2 name)) $1 ∧
    (sf_formula (if universal then SFImpl else SFAnd) $1 (code_lift2 w) $0 ∧
    sf_formula (if universal then SFAll else SFEx) $0 zero (code_lift2 v))).
Local Opaque holds sf_formula.

Lemma ssr_quantifier_formula_correct M rho universal name w v :
  holds M rho(ssr_quantifier_formula universal name w v) <->
  ssr_quantifier M universal (evalM M rho name)(evalM M rho w)(evalM M rho v).
Proof.
  unfold ssr_quantifier_formula,ssr_quantifier.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. setoid_rewrite substitution_map_eval_succ. setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Lemma ssr_quantifier_total M universal name w :exists v,ssr_quantifier M universal name w v.
Proof.
  destruct(sf_relation_total M SFMember (zeroM M)(succM M name)) as(guard&HG).
  destruct(sf_relation_total M (if universal then SFImpl else SFAnd) guard w) as(mid&HM).
  destruct(sf_relation_total M (if universal then SFAll else SFEx) mid (zeroM M)) as(v&HV).
  exists v,guard,mid. auto.
Qed.
Lemma ssr_quantifier_functional M universal name w v v' :
  ssr_quantifier M universal name w v ->ssr_quantifier M universal name w v' ->v=v'.
Proof.
  intros(g&m&HG&HM&HV)(g'&m'&HG'&HM'&HV').
  pose proof(sf_relation_functional M SFMember _ _ g g' HG HG') as E. subst g'.
  pose proof(sf_relation_functional M _ g w m m' HM HM') as E. subst m'.
  exact(sf_relation_functional M _ m (zeroM M) v v' HV HV').
Qed.

Definition ssr_unary M r p :=exists name f v a w,
  sr_record M name f v r /\sr_record M (succM M name) a w p /\
  ((sf_relation M SFAll a (zeroM M) f /\ssr_quantifier M true name w v) \/
   (sf_relation M SFEx a (zeroM M) f /\ssr_quantifier M false name w v)).
Definition ssr_unary_formula :form :=
  ∃∃∃∃∃(sr_record_formula $4 $3 $2 $5 ∧(sr_record_formula (σ $4) $1 $0 $6 ∧
    ((sf_formula SFAll $1 zero $3 ∧ssr_quantifier_formula true $4 $0 $2) ∨
     (sf_formula SFEx $1 zero $3 ∧ssr_quantifier_formula false $4 $0 $2)))).
Local Opaque sr_record_formula ssr_quantifier_formula.
Lemma ssr_unary_formula_correct M rho r p :
  holds M (r .:p .:rho) ssr_unary_formula <->ssr_unary M r p.
Proof.
  unfold ssr_unary_formula,ssr_unary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  setoid_rewrite sr_record_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite ssr_quantifier_formula_correct. setoid_rewrite substitution_map_eval_succ. reflexivity.
Qed.
Lemma ssr_unary_bound :bounded 2 ssr_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_set_relativization_rules :NumericalRules :=
  {|rule_base_formula:=sr_base_formula;rule_base_bound:=sr_base_bound;
    rule_unary_formula:=ssr_unary_formula;rule_unary_bound:=ssr_unary_bound;
    rule_binary_formula:=sr_binary_formula;rule_binary_bound:=sr_binary_bound|}.
Lemma ssr_rule_base M r :trace_base M source_set_relativization_rules r <->sr_base M r.
Proof. apply sr_base_formula_correct. Qed.
Lemma ssr_rule_unary M r p :trace_unary M source_set_relativization_rules r p <->ssr_unary M r p.
Proof. apply ssr_unary_formula_correct. Qed.
Lemma ssr_rule_binary M r p q :trace_binary M source_set_relativization_rules r p q <->sr_binary M r p q.
Proof. apply sr_binary_formula_correct. Qed.

Print Assumptions ssr_quantifier_formula_correct.
Print Assumptions ssr_quantifier_functional.
Print Assumptions ssr_unary_formula_correct.
