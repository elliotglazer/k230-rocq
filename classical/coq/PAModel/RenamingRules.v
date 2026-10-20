(** Arithmetic trace rules for de Bruijn renaming. Record fields are source,
    prefix dividend, modulus, length, tail delta, inert padding, output.
    The public interface fixes padding to zero. Invalid sources map to zero. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SetCodeDescent
  NumericalEnvironments NumericalRenamingMaps CodeTuples RenamingPayloads NumericalTraces.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition renaming_lift5 (t : term) := t`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma renaming_lift5_correct M rho a b c d e t :
  evalM M (e .: d .: c .: b .: a .: rho) (renaming_lift5 t) = evalM M rho t.
Proof. unfold evalM,renaming_lift5. now rewrite !eval_up. Qed.
Lemma renaming_eval_succ M rho t :
  evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.


Definition renaming_atom_case M equality f b c n k t v :=
  exists a d x y, sf_relation M (renaming_source_atom equality) a d f /\
    renaming_lookup M b c n k a x /\ renaming_lookup M b c n k d y /\
    renaming_atom M equality x y t k v.
Definition renaming_atom_case_formula equality (f b c n k t v : term) : form :=
  ∃∃∃∃ (sf_formula (renaming_source_atom equality) $3 $2 (lift4 f) ∧
    renaming_lookup_formula (lift4 b) (lift4 c) (lift4 n) (lift4 k) $3 $1 ∧
    renaming_lookup_formula (lift4 b) (lift4 c) (lift4 n) (lift4 k) $2 $0 ∧
    renaming_atom_formula equality $1 $0 (lift4 t) (lift4 k) (lift4 v)).

Local Opaque holds sf_formula renaming_lookup_formula renaming_atom_formula.
Lemma renaming_atom_case_formula_correct M rho equality f b c n k t v :
  holds M rho (renaming_atom_case_formula equality f b c n k t v) <->
  renaming_atom_case M equality (evalM M rho f) (evalM M rho b)
    (evalM M rho c) (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold renaming_atom_case_formula,renaming_atom_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. setoid_rewrite renaming_lookup_formula_correct.
  setoid_rewrite renaming_atom_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition renaming_leaf M f b c n k t v :=
  ((f=zeroM M \/ sf_invalid M f) /\ v=zeroM M) \/
  renaming_atom_case M false f b c n k t v \/ renaming_atom_case M true f b c n k t v.
Definition renaming_leaf_formula (f b c n k t v : term) : form :=
  (((f == zero) ∨ sf_invalid_formula f) ∧ (v == zero)) ∨
  (renaming_atom_case_formula false f b c n k t v ∨
   renaming_atom_case_formula true f b c n k t v).

Local Opaque renaming_atom_case_formula sf_invalid_formula.
Lemma renaming_leaf_formula_correct M rho f b c n k t v :
  holds M rho (renaming_leaf_formula f b c n k t v) <->
  renaming_leaf M (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v).
Proof.
  unfold renaming_leaf_formula,renaming_leaf.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or.
  setoid_rewrite sf_invalid_formula_correct.
  setoid_rewrite renaming_atom_case_formula_correct.
  reflexivity.
Qed.

Definition renaming_base M r := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\ renaming_leaf M f b c n k t v.
Definition renaming_base_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    renaming_leaf_formula $6 $5 $4 $3 $2 $1 $0).

Local Opaque tuple7_formula renaming_leaf_formula.
Lemma renaming_base_formula_correct M rho r :
  holds M (r .: rho) renaming_base_formula <-> renaming_base M r.
Proof.
  unfold renaming_base_formula,renaming_base.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite renaming_leaf_formula_correct.
  reflexivity.
Qed.

Definition renaming_unary_case M universal f b c n k t v p :=
  exists a d e m w,
    tuple7_graph M a d e m k t w p /\
    renaming_lift M b c n k d e m /\
    sf_relation M (renaming_source_quantifier universal) a (zeroM M) f /\
    renaming_quantifier M universal k t w v.
Definition renaming_unary_case_formula universal (f b c n k t v p : term) : form :=
  ∃∃∃∃∃ (tuple7_formula $4 $3 $2 $1 (renaming_lift5 k) (renaming_lift5 t) $0
      (renaming_lift5 p) ∧
    renaming_lift_formula (renaming_lift5 b) (renaming_lift5 c)
      (renaming_lift5 n) (renaming_lift5 k) $3 $2 $1 ∧
    sf_formula (renaming_source_quantifier universal) $4 zero (renaming_lift5 f) ∧
    renaming_quantifier_formula universal (renaming_lift5 k) (renaming_lift5 t)
      $0 (renaming_lift5 v)).

Local Opaque renaming_lift_formula renaming_quantifier_formula.
Lemma renaming_unary_case_formula_correct M rho universal f b c n k t v p :
  holds M rho (renaming_unary_case_formula universal f b c n k t v p) <->
  renaming_unary_case M universal (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v) (evalM M rho p).
Proof.
  unfold renaming_unary_case_formula,renaming_unary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite renaming_lift_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite renaming_quantifier_formula_correct.
  try setoid_rewrite renaming_eval_succ.
  try setoid_rewrite renaming_lift5_correct.
  split; intros [a [d [e [m [w H]]]]]; exists a,d,e,m,w; tauto.
Qed.

Definition renaming_unary M r p := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (renaming_unary_case M true f b c n k t v p \/
     renaming_unary_case M false f b c n k t v p).
Definition renaming_unary_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (renaming_unary_case_formula true $6 $5 $4 $3 $2 $1 $0 $8 ∨
     renaming_unary_case_formula false $6 $5 $4 $3 $2 $1 $0 $8)).

Local Opaque renaming_unary_case_formula.
Lemma renaming_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) renaming_unary_formula <-> renaming_unary M r p.
Proof.
  unfold renaming_unary_formula,renaming_unary.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite renaming_unary_case_formula_correct. reflexivity.
Qed.

Definition renaming_binary_case M h f b c n k t v p q :=
  exists a d x y,
    tuple7_graph M a b c n k t x p /\ tuple7_graph M d b c n k t y q /\
    sf_relation M h a d f /\ renaming_binary M h x y v.
Definition renaming_binary_case_formula h (f b c n k t v p q : term) : form :=
  ∃∃∃∃ (tuple7_formula $3 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $1 (lift4 p) ∧
    tuple7_formula $2 (lift4 b) (lift4 c) (lift4 n) (lift4 k) (lift4 t) $0 (lift4 q) ∧
    sf_formula h $3 $2 (lift4 f) ∧ renaming_binary_formula h $1 $0 (lift4 v)).

Local Opaque renaming_binary_formula.
Lemma renaming_binary_case_formula_correct M rho h f b c n k t v p q :
  holds M rho (renaming_binary_case_formula h f b c n k t v p q) <->
  renaming_binary_case M h (evalM M rho f) (evalM M rho b) (evalM M rho c)
    (evalM M rho n) (evalM M rho k) (evalM M rho t) (evalM M rho v)
    (evalM M rho p) (evalM M rho q).
Proof.
  unfold renaming_binary_case_formula,renaming_binary_case.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite tuple7_formula_correct. setoid_rewrite sf_formula_correct.
  try setoid_rewrite renaming_binary_formula_correct. try setoid_rewrite lift4_correct.
  split; intros [a [d [x [y H]]]]; exists a,d,x,y; tauto.
Qed.

Definition renaming_binary_rule M r p q := exists f b c n k t v,
  tuple7_graph M f b c n k t v r /\
    (renaming_binary_case M SFAnd f b c n k t v p q \/
     renaming_binary_case M SFOr f b c n k t v p q \/
     renaming_binary_case M SFImpl f b c n k t v p q).
Definition renaming_binary_rule_formula : form :=
  ∃∃∃∃∃∃∃ (tuple7_formula $6 $5 $4 $3 $2 $1 $0 $7 ∧
    (renaming_binary_case_formula SFAnd $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
     (renaming_binary_case_formula SFOr $6 $5 $4 $3 $2 $1 $0 $8 $9 ∨
      renaming_binary_case_formula SFImpl $6 $5 $4 $3 $2 $1 $0 $8 $9))).

Local Opaque renaming_binary_case_formula.
Lemma renaming_binary_rule_formula_correct M rho r p q :
  holds M (r .: p .: q .: rho) renaming_binary_rule_formula <-> renaming_binary_rule M r p q.
Proof.
  unfold renaming_binary_rule_formula,renaming_binary_rule.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or. setoid_rewrite tuple7_formula_correct.
  setoid_rewrite renaming_binary_case_formula_correct. reflexivity.
Qed.

Lemma renaming_base_bound : bounded 1 renaming_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma renaming_unary_bound : bounded 2 renaming_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma renaming_binary_rule_bound : bounded 3 renaming_binary_rule_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition renaming_rules : NumericalRules :=
  {| rule_base_formula := renaming_base_formula;
     rule_base_bound := renaming_base_bound;
     rule_unary_formula := renaming_unary_formula;
     rule_unary_bound := renaming_unary_bound;
     rule_binary_formula := renaming_binary_rule_formula;
     rule_binary_bound := renaming_binary_rule_bound |}.

Lemma renaming_rule_base M r : trace_base M renaming_rules r <-> renaming_base M r.
Proof. apply renaming_base_formula_correct. Qed.
Lemma renaming_rule_unary M r p : trace_unary M renaming_rules r p <-> renaming_unary M r p.
Proof. apply renaming_unary_formula_correct. Qed.
Lemma renaming_rule_binary M r p q :
  trace_binary M renaming_rules r p q <-> renaming_binary_rule M r p q.
Proof. apply renaming_binary_rule_formula_correct. Qed.

Print Assumptions renaming_atom_case_formula_correct.
Print Assumptions renaming_base_formula_correct.
Print Assumptions renaming_unary_formula_correct.
Print Assumptions renaming_binary_rule_formula_correct.
Print Assumptions renaming_base_bound.
Print Assumptions renaming_unary_bound.
Print Assumptions renaming_binary_rule_bound.
