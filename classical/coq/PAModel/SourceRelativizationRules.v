(** Arithmetic computation rules for relational source relativization.
    The domain formula is inserted unchanged under each new binder. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SetFormulaCodes SetCodeDescent CodeTuples NumericalTraces SentenceBounds FreshNames.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition sr_record M d f v r :=
  tuple7_graph M d f v (zeroM M) (zeroM M) (zeroM M) (zeroM M) r.
Definition sr_record_formula (d f v r:term) : form :=
  tuple7_formula d f v zero zero zero zero r.
Lemma sr_record_formula_correct M rho d f v r :
  holds M rho (sr_record_formula d f v r) <->
  sr_record M (evalM M rho d) (evalM M rho f) (evalM M rho v) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Lemma sr_record_total M d f v : exists r,sr_record M d f v r.
Proof. apply tuple7_total. Qed.
Lemma sr_record_injective M d f v d' f' v' r :
  sr_record M d f v r -> sr_record M d' f' v' r -> d=d' /\ f=f' /\ v=v'.
Proof.
  intros H H'. destruct (tuple7_injective M d f v _ _ _ _ d' f' v' _ _ _ _ r H H')
    as [Hd [Hf [Hv _]]]. auto.
Qed.

Definition sr_leaf M f v :=
  ((f=zeroM M \/ sf_invalid M f) /\ v=zeroM M) \/
  (exists a b,(sf_relation M SFMember a b f \/ sf_relation M SFEqual a b f) /\ v=f).
Definition sr_leaf_formula (f v:term) : form :=
  ((f==zero ∨ sf_invalid_formula f) ∧ v==zero) ∨
  ∃∃ ((sf_formula SFMember $1 $0 (code_lift2 f) ∨
        sf_formula SFEqual $1 $0 (code_lift2 f)) ∧ code_lift2 v==code_lift2 f).
Local Opaque sf_formula sf_invalid_formula.
Lemma sr_leaf_formula_correct M rho f v :
  holds M rho (sr_leaf_formula f v) <-> sr_leaf M (evalM M rho f) (evalM M rho v).
Proof.
  unfold sr_leaf_formula,sr_leaf.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_or.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_or.
  setoid_rewrite sf_invalid_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite fresh_holds_eq.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Definition sr_quantifier M (universal:bool) d w v := exists mid,
  sf_relation M (if universal then SFImpl else SFAnd) d w mid /\
  sf_relation M (if universal then SFAll else SFEx) mid (zeroM M) v.
Definition sr_quantifier_formula (universal:bool) (d w v:term) : form :=
  ∃ (sf_formula (if universal then SFImpl else SFAnd) d`[↑] w`[↑] $0 ∧
    sf_formula (if universal then SFAll else SFEx) $0 zero v`[↑]).
Lemma sr_quantifier_formula_correct M rho universal d w v :
  holds M rho (sr_quantifier_formula universal d w v) <->
  sr_quantifier M universal (evalM M rho d) (evalM M rho w) (evalM M rho v).
Proof.
  unfold sr_quantifier_formula,sr_quantifier.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Lemma sr_quantifier_total M universal d w : exists v,sr_quantifier M universal d w v.
Proof.
  destruct (sf_relation_total M (if universal then SFImpl else SFAnd) d w) as [mid HM].
  destruct (sf_relation_total M (if universal then SFAll else SFEx) mid (zeroM M)) as [v HV].
  exists v,mid. auto.
Qed.

Definition sr_base M r := exists d f v,sr_record M d f v r /\ sr_leaf M f v.
Definition sr_base_formula : form :=
  ∃∃∃ (sr_record_formula $2 $1 $0 $3 ∧ sr_leaf_formula $1 $0).
Local Opaque sr_record_formula sr_leaf_formula sr_quantifier_formula.
Lemma sr_base_formula_correct M rho r : holds M (r .: rho) sr_base_formula <-> sr_base M r.
Proof.
  unfold sr_base_formula,sr_base. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite sr_record_formula_correct.
  setoid_rewrite sr_leaf_formula_correct. reflexivity.
Qed.

Definition sr_unary M r p := exists d f v a w,
  sr_record M d f v r /\ sr_record M d a w p /\
  ((sf_relation M SFAll a (zeroM M) f /\ sr_quantifier M true d w v) \/
   (sf_relation M SFEx a (zeroM M) f /\ sr_quantifier M false d w v)).
Definition sr_unary_formula : form :=
  ∃∃∃∃∃ (sr_record_formula $4 $3 $2 $5 ∧ (sr_record_formula $4 $1 $0 $6 ∧
    ((sf_formula SFAll $1 zero $3 ∧ sr_quantifier_formula true $4 $0 $2) ∨
     (sf_formula SFEx $1 zero $3 ∧ sr_quantifier_formula false $4 $0 $2)))).
Lemma sr_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) sr_unary_formula <-> sr_unary M r p.
Proof.
  unfold sr_unary_formula,sr_unary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite holds_or.
  repeat setoid_rewrite holds_and. setoid_rewrite sr_record_formula_correct.
  setoid_rewrite sf_formula_correct. setoid_rewrite sr_quantifier_formula_correct. reflexivity.
Qed.

Definition sr_binary_heads M a b f x y v :=
  (sf_relation M SFAnd a b f /\ sf_relation M SFAnd x y v) \/
  (sf_relation M SFOr a b f /\ sf_relation M SFOr x y v) \/
  (sf_relation M SFImpl a b f /\ sf_relation M SFImpl x y v).
Definition sr_binary_heads_formula (a b f x y v:term) : form :=
  (sf_formula SFAnd a b f ∧ sf_formula SFAnd x y v) ∨
  ((sf_formula SFOr a b f ∧ sf_formula SFOr x y v) ∨
   (sf_formula SFImpl a b f ∧ sf_formula SFImpl x y v)).
Lemma sr_binary_heads_formula_correct M rho a b f x y v :
  holds M rho (sr_binary_heads_formula a b f x y v) <->
  sr_binary_heads M (evalM M rho a) (evalM M rho b) (evalM M rho f)
    (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof.
  unfold sr_binary_heads_formula,sr_binary_heads.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  setoid_rewrite sf_formula_correct. reflexivity.
Qed.

Definition sr_binary M r p q := exists d f v a b x y,
  sr_record M d f v r /\ sr_record M d a x p /\ sr_record M d b y q /\
  sr_binary_heads M a b f x y v.
Definition sr_binary_formula : form :=
  ∃∃∃∃∃∃∃ (sr_record_formula $6 $5 $4 $7 ∧
    (sr_record_formula $6 $3 $1 $8 ∧ (sr_record_formula $6 $2 $0 $9 ∧
      sr_binary_heads_formula $3 $2 $5 $1 $0 $4))).
Local Opaque sr_binary_heads_formula.
Lemma sr_binary_formula_correct M rho r p q :
  holds M (r .: p .: q .: rho) sr_binary_formula <-> sr_binary M r p q.
Proof.
  unfold sr_binary_formula,sr_binary. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite sr_record_formula_correct.
  setoid_rewrite sr_binary_heads_formula_correct. reflexivity.
Qed.

Lemma sr_base_bound : bounded 1 sr_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma sr_unary_bound : bounded 2 sr_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma sr_binary_bound : bounded 3 sr_binary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Definition source_relativization_rules : NumericalRules :=
  {| rule_base_formula:=sr_base_formula;rule_base_bound:=sr_base_bound;
     rule_unary_formula:=sr_unary_formula;rule_unary_bound:=sr_unary_bound;
     rule_binary_formula:=sr_binary_formula;rule_binary_bound:=sr_binary_bound |}.
Lemma sr_rule_base M r : trace_base M source_relativization_rules r <-> sr_base M r.
Proof. apply sr_base_formula_correct. Qed.
Lemma sr_rule_unary M r p : trace_unary M source_relativization_rules r p <-> sr_unary M r p.
Proof. apply sr_unary_formula_correct. Qed.
Lemma sr_rule_binary M r p q : trace_binary M source_relativization_rules r p q <-> sr_binary M r p q.
Proof. apply sr_binary_formula_correct. Qed.

Print Assumptions sr_record_formula_correct.
Print Assumptions sr_leaf_formula_correct.
Print Assumptions sr_quantifier_formula_correct.
Print Assumptions sr_binary_formula_correct.
