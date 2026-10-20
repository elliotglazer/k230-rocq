(** Arithmetic trace rules for de Bruijn substitution. Record fields are source,
    prefix dividend, modulus, length, tail base, inert padding, output.
    The public interface fixes padding to zero. Invalid sources map to zero. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalSubstitutionMaps CodeTuples SubstitutionPayloads NumericalTraces.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition substitution_lift5 (t : term) := t`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma substitution_lift5_correct M rho a b c d e t :
  evalM M (e .: d .: c .: b .: a .: rho) (substitution_lift5 t) = evalM M rho t.
Proof. unfold evalM,substitution_lift5. now rewrite !eval_up. Qed.
Lemma substitution_eval_succ M rho t :
  evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.


Definition substitution_atom_case M equality f b c n k t v :=
  exists a d x y, sf_relation M (substitution_source_atom equality) a d f /\
    substitution_lookup M b c n k a x /\ substitution_lookup M b c n k d y /\
    substitution_atom M equality x y t k v.
Definition substitution_atom_case_formula equality (f b c n k t v : term) : form :=
  ∃∃∃∃ (sf_formula (substitution_source_atom equality) $3 $2 (lift4 f) ∧
    substitution_lookup_formula (lift4 b) (lift4 c) (lift4 n) (lift4 k) $3 $1 ∧
    substitution_lookup_formula (lift4 b) (lift4 c) (lift4 n) (lift4 k) $2 $0 ∧
    substitution_atom_formula equality $1 $0 (lift4 t) (lift4 k) (lift4 v)).

Local Opaque holds sf_formula substitution_lookup_formula substitution_atom_formula.
Lemma substitution_atom_case_formula_correct M rho equality f b c n k t v :
  holds M rho (substitution_atom_case_formula equality f b c n k t v) <->
  substitution_atom_case M equality (evalM M rho f) (evalM M rho b)
    (evalM M rho c) (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold substitution_atom_case_formula,substitution_atom_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite substitution_atom_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition substitution_leaf M f b c n k t v :=
  ((f=zeroM M \/ sf_invalid M f) /\ v=zeroM M) \/
  substitution_atom_case M false f b c n k t v \/ substitution_atom_case M true f b c n k t v.
Definition substitution_leaf_formula (f b c n k t v : term) : form :=
  (((f == zero) ∨ sf_invalid_formula f) ∧ (v == zero)) ∨
  (substitution_atom_case_formula false f b c n k t v ∨
   substitution_atom_case_formula true f b c n k t v).

Local Opaque substitution_atom_case_formula sf_invalid_formula.
Lemma substitution_leaf_formula_correct M rho f b c n k t v :
  holds M rho (substitution_leaf_formula f b c n k t v) <->
  substitution_leaf M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold substitution_leaf_formula,substitution_leaf.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or.
  setoid_rewrite sf_invalid_formula_correct.
  setoid_rewrite substitution_atom_case_formula_correct.
  reflexivity.
Qed.

Definition substitution_base M r := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\ substitution_leaf M f b c n k t v.
Definition substitution_base_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    substitution_leaf_formula $6 $5 $4 $3 $2 $1 $0).

Local Opaque tuple7_formula substitution_leaf_formula.
Lemma substitution_base_formula_correct M rho r :
  holds M (r .: rho) substitution_base_formula <-> substitution_base M r.
Proof.
  unfold substitution_base_formula,substitution_base.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite substitution_leaf_formula_correct.
  reflexivity.
Qed.

Definition substitution_unary_case M universal f b c n k t v p :=
  exists a d e m w,
    tuple7_graph M a d e m (succM M k) t w p /\
    substitution_lift M b c n k d e m /\
    sf_relation M (substitution_source_quantifier universal) a (zeroM M) f /\
    substitution_quantifier M universal k t w v.
Definition substitution_unary_case_formula universal (f b c n k t v p : term) : form :=
  ∃∃∃∃∃ (tuple7_formula $4 $3 $2 $1 (σ (substitution_lift5 k)) (substitution_lift5 t) $0
      (substitution_lift5 p) ∧
    substitution_lift_formula (substitution_lift5 b) (substitution_lift5 c)
      (substitution_lift5 n) (substitution_lift5 k) $3 $2 $1 ∧
    sf_formula (substitution_source_quantifier universal) $4 zero (substitution_lift5 f) ∧
    substitution_quantifier_formula universal (substitution_lift5 k) (substitution_lift5 t)
      $0 (substitution_lift5 v)).

Local Opaque substitution_lift_formula substitution_quantifier_formula.
Lemma substitution_unary_case_formula_correct M rho universal f b c n k t v p :
  holds M rho (substitution_unary_case_formula universal f b c n k t v p) <->
  substitution_unary_case M universal (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v) (evalM M rho p).
Proof.
  unfold substitution_unary_case_formula,substitution_unary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite substitution_lift_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite substitution_quantifier_formula_correct.
  try setoid_rewrite substitution_eval_succ.
  try setoid_rewrite substitution_lift5_correct.
  split; intros [a [d [e [m [w H]]]]]; exists a,d,e,m,w; tauto.
Qed.

Definition substitution_unary M r p := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (substitution_unary_case M true f b c n k t v p \/
     substitution_unary_case M false f b c n k t v p).
Definition substitution_unary_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (substitution_unary_case_formula true $6 $5 $4 $3 $2 $1 $0 $8 ∨
     substitution_unary_case_formula false $6 $5 $4 $3 $2 $1 $0 $8)).

Local Opaque substitution_unary_case_formula.
Lemma substitution_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) substitution_unary_formula <-> substitution_unary M r p.
Proof.
  unfold substitution_unary_formula,substitution_unary.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite substitution_unary_case_formula_correct. reflexivity.
Qed.

Definition substitution_binary_case M h f b c n k t v p q :=
  exists a d x y,
    tuple7_graph M a b c n k t x p /\ tuple7_graph M d b c n k t y q /\
    sf_relation M h a d f /\ substitution_binary M h x y v.
Definition substitution_binary_case_formula h (f b c n k t v p q : term) : form :=
  ∃∃∃∃ (tuple7_formula $3 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $1 (lift4 p) ∧
    tuple7_formula $2 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $0 (lift4 q) ∧
    sf_formula h $3 $2 (lift4 f) ∧ substitution_binary_formula h $1 $0 (lift4 v)).

Local Opaque substitution_binary_formula.
Lemma substitution_binary_case_formula_correct M rho h f b c n k t v p q :
  holds M rho (substitution_binary_case_formula h f b c n k t v p q) <->
  substitution_binary_case M h (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v)
    (evalM M rho p) (evalM M rho q).
Proof.
  unfold substitution_binary_case_formula,substitution_binary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite sf_formula_correct.
  try setoid_rewrite substitution_binary_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition substitution_binary_rule M r p q := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (substitution_binary_case M SFAnd f b c n k t v p q \/
     substitution_binary_case M SFOr f b c n k t v p q \/
     substitution_binary_case M SFImpl f b c n k t v p q).
Definition substitution_binary_rule_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (substitution_binary_case_formula SFAnd $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
     (substitution_binary_case_formula SFOr $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
      substitution_binary_case_formula SFImpl $6 $5 $4 $3 $2 $1 $0 $8 $9))).

Local Opaque substitution_binary_case_formula.
Lemma substitution_binary_rule_formula_correct M rho r p q :
  holds M (r .: p .: q .: rho) substitution_binary_rule_formula <-> substitution_binary_rule M r p q.
Proof.
  unfold substitution_binary_rule_formula,substitution_binary_rule.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite substitution_binary_case_formula_correct. reflexivity.
Qed.

Lemma substitution_base_bound : bounded 1 substitution_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma substitution_unary_bound : bounded 2 substitution_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma substitution_binary_rule_bound : bounded 3 substitution_binary_rule_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition substitution_rules : NumericalRules :=
  {| rule_base_formula := substitution_base_formula;
     rule_base_bound := substitution_base_bound;
     rule_unary_formula := substitution_unary_formula;
     rule_unary_bound := substitution_unary_bound;
     rule_binary_formula := substitution_binary_rule_formula;
     rule_binary_bound := substitution_binary_rule_bound |}.

Lemma substitution_rule_base M r : trace_base M substitution_rules r <-> substitution_base M r.
Proof. apply substitution_base_formula_correct. Qed.
Lemma substitution_rule_unary M r p : trace_unary M substitution_rules r p <-> substitution_unary M r p.
Proof. apply substitution_unary_formula_correct. Qed.
Lemma substitution_rule_binary M r p q :
  trace_binary M substitution_rules r p q <-> substitution_binary_rule M r p q.
Proof. apply substitution_binary_rule_formula_correct. Qed.

Print Assumptions substitution_atom_case_formula_correct.
Print Assumptions substitution_base_formula_correct.
Print Assumptions substitution_unary_formula_correct.
Print Assumptions substitution_binary_rule_formula_correct.
Print Assumptions substitution_base_bound.
Print Assumptions substitution_unary_bound.
Print Assumptions substitution_binary_rule_bound.
