(** Local arithmetic rules for quoting eight-tag source formulas into the
    named quotient language. Each row carries the complete recursive call:
    source, environment dividend, modulus, length, fresh name, domain, output.
    Invalid top-level source codes are assigned falsity for totality only. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments CodeTuples QuotationPayloads NumericalTraces.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition quotation_lift5 (t : term) := t`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma quotation_lift5_correct M rho a b c d e t :
  evalM M (e .: d .: c .: b .: a .: rho) (quotation_lift5 t) = evalM M rho t.
Proof. unfold evalM,quotation_lift5. now rewrite !eval_up. Qed.
Lemma quotation_eval_succ M rho t :
  evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.

Definition quotation_source_atom (equality : bool) := if equality then SFEqual else SFMember.
Definition quotation_source_quantifier (universal : bool) := if universal then SFAll else SFEx.

Definition quotation_atom_case M equality f b c n k t v :=
  exists a d x y, sf_relation M (quotation_source_atom equality) a d f /\
    environment_lookup M b c n a x /\ environment_lookup M b c n d y /\
    quotation_atom M equality x y t k v.
Definition quotation_atom_case_formula equality (f b c n k t v : term) : form :=
  ∃∃∃∃ (sf_formula (quotation_source_atom equality) $3 $2 (lift4 f) ∧
    environment_lookup_formula (lift4 b) (lift4 c) (lift4 n) $3 $1 ∧
    environment_lookup_formula (lift4 b) (lift4 c) (lift4 n) $2 $0 ∧
    quotation_atom_formula equality $1 $0 (lift4 t) (lift4 k) (lift4 v)).

Local Opaque holds sf_formula environment_lookup_formula quotation_atom_formula.
Lemma quotation_atom_case_formula_correct M rho equality f b c n k t v :
  holds M rho (quotation_atom_case_formula equality f b c n k t v) <->
  quotation_atom_case M equality (evalM M rho f) (evalM M rho b)
    (evalM M rho c) (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold quotation_atom_case_formula,quotation_atom_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. setoid_rewrite environment_lookup_formula_correct.
  setoid_rewrite quotation_atom_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition quotation_leaf M f b c n k t v :=
  ((f=zeroM M \/ sf_invalid M f) /\ v=code_numeral M 1) \/
  quotation_atom_case M false f b c n k t v \/ quotation_atom_case M true f b c n k t v.
Definition quotation_leaf_formula (f b c n k t v : term) : form :=
  (((f == zero) ∨ sf_invalid_formula f) ∧ (v == num 1)) ∨
  (quotation_atom_case_formula false f b c n k t v ∨
   quotation_atom_case_formula true f b c n k t v).

Local Opaque quotation_atom_case_formula sf_invalid_formula.
Lemma quotation_leaf_formula_correct M rho f b c n k t v :
  holds M rho (quotation_leaf_formula f b c n k t v) <->
  quotation_leaf M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold quotation_leaf_formula,quotation_leaf.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or.
  setoid_rewrite sf_invalid_formula_correct.
  setoid_rewrite quotation_atom_case_formula_correct.
  reflexivity.
Qed.

Definition quotation_base M r := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\ quotation_leaf M f b c n k t v.
Definition quotation_base_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    quotation_leaf_formula $6 $5 $4 $3 $2 $1 $0).

Local Opaque tuple7_formula quotation_leaf_formula.
Lemma quotation_base_formula_correct M rho r :
  holds M (r .: rho) quotation_base_formula <-> quotation_base M r.
Proof.
  unfold quotation_base_formula,quotation_base.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite quotation_leaf_formula_correct.
  reflexivity.
Qed.

Definition quotation_unary_case M universal f b c n k t v p :=
  exists a d e m w,
    tuple7_graph M a d e m (succM M k) t w p /\
    environment_cons M b c n k d e m /\
    sf_relation M (quotation_source_quantifier universal) a (zeroM M) f /\
    quotation_quantifier M universal k t w v.
Definition quotation_unary_case_formula universal (f b c n k t v p : term) : form :=
  ∃∃∃∃∃ (tuple7_formula $4 $3 $2 $1 (σ (quotation_lift5 k)) (quotation_lift5 t) $0
      (quotation_lift5 p) ∧
    environment_cons_formula (quotation_lift5 b) (quotation_lift5 c)
      (quotation_lift5 n) (quotation_lift5 k) $3 $2 $1 ∧
    sf_formula (quotation_source_quantifier universal) $4 zero (quotation_lift5 f) ∧
    quotation_quantifier_formula universal (quotation_lift5 k) (quotation_lift5 t)
      $0 (quotation_lift5 v)).

Local Opaque environment_cons_formula quotation_quantifier_formula.
Lemma quotation_unary_case_formula_correct M rho universal f b c n k t v p :
  holds M rho (quotation_unary_case_formula universal f b c n k t v p) <->
  quotation_unary_case M universal (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v) (evalM M rho p).
Proof.
  unfold quotation_unary_case_formula,quotation_unary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite environment_cons_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite quotation_quantifier_formula_correct.
  setoid_rewrite quotation_eval_succ.
  try setoid_rewrite quotation_lift5_correct.
  split; intros [a [d [e [m [w H]]]]]; exists a,d,e,m,w; tauto.
Qed.

Definition quotation_unary M r p := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (quotation_unary_case M true f b c n k t v p \/
     quotation_unary_case M false f b c n k t v p).
Definition quotation_unary_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (quotation_unary_case_formula true $6 $5 $4 $3 $2 $1 $0 $8 ∨
     quotation_unary_case_formula false $6 $5 $4 $3 $2 $1 $0 $8)).

Local Opaque quotation_unary_case_formula.
Lemma quotation_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) quotation_unary_formula <-> quotation_unary M r p.
Proof.
  unfold quotation_unary_formula,quotation_unary.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite quotation_unary_case_formula_correct. reflexivity.
Qed.

Definition quotation_binary_case M h f b c n k t v p q :=
  exists a d x y,
    tuple7_graph M a b c n k t x p /\ tuple7_graph M d b c n k t y q /\
    sf_relation M h a d f /\ quotation_binary M h x y v.
Definition quotation_binary_case_formula h (f b c n k t v p q : term) : form :=
  ∃∃∃∃ (tuple7_formula $3 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $1 (lift4 p) ∧
    tuple7_formula $2 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $0 (lift4 q) ∧
    sf_formula h $3 $2 (lift4 f) ∧ quotation_binary_formula h $1 $0 (lift4 v)).

Local Opaque quotation_binary_formula.
Lemma quotation_binary_case_formula_correct M rho h f b c n k t v p q :
  holds M rho (quotation_binary_case_formula h f b c n k t v p q) <->
  quotation_binary_case M h (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v)
    (evalM M rho p) (evalM M rho q).
Proof.
  unfold quotation_binary_case_formula,quotation_binary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite quotation_binary_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition quotation_binary_rule M r p q := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (quotation_binary_case M SFAnd f b c n k t v p q \/
     quotation_binary_case M SFOr f b c n k t v p q \/
     quotation_binary_case M SFImpl f b c n k t v p q).
Definition quotation_binary_rule_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (quotation_binary_case_formula SFAnd $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
     (quotation_binary_case_formula SFOr $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
      quotation_binary_case_formula SFImpl $6 $5 $4 $3 $2 $1 $0 $8 $9))).

Local Opaque quotation_binary_case_formula.
Lemma quotation_binary_rule_formula_correct M rho r p q :
  holds M (r .: p .: q .: rho) quotation_binary_rule_formula <-> quotation_binary_rule M r p q.
Proof.
  unfold quotation_binary_rule_formula,quotation_binary_rule.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite quotation_binary_case_formula_correct. reflexivity.
Qed.

Lemma quotation_base_bound : bounded 1 quotation_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma quotation_unary_bound : bounded 2 quotation_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma quotation_binary_rule_bound : bounded 3 quotation_binary_rule_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition quotation_rules : NumericalRules :=
  {| rule_base_formula := quotation_base_formula;
     rule_base_bound := quotation_base_bound;
     rule_unary_formula := quotation_unary_formula;
     rule_unary_bound := quotation_unary_bound;
     rule_binary_formula := quotation_binary_rule_formula;
     rule_binary_bound := quotation_binary_rule_bound |}.

Lemma quotation_rule_base M r : trace_base M quotation_rules r <-> quotation_base M r.
Proof. apply quotation_base_formula_correct. Qed.
Lemma quotation_rule_unary M r p : trace_unary M quotation_rules r p <-> quotation_unary M r p.
Proof. apply quotation_unary_formula_correct. Qed.
Lemma quotation_rule_binary M r p q :
  trace_binary M quotation_rules r p q <-> quotation_binary_rule M r p q.
Proof. apply quotation_binary_rule_formula_correct. Qed.

Print Assumptions quotation_atom_case_formula_correct.
Print Assumptions quotation_base_formula_correct.
Print Assumptions quotation_unary_formula_correct.
Print Assumptions quotation_binary_rule_formula_correct.
Print Assumptions quotation_base_bound.
Print Assumptions quotation_unary_bound.
Print Assumptions quotation_binary_rule_bound.
