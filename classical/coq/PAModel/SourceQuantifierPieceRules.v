(** Arithmetic access paths to the quantified bodies enumerated by pcs.
    The context bound increases exactly when a quantifier is crossed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
  SetCodeDescent SourceBounded CodeTuples NumericalTraces SentenceBounds NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition qpiece_record M f n k a r :=
  tuple7_graph M f n k a (zeroM M) (zeroM M) (zeroM M) r.
Definition qpiece_record_formula (f n k a r:term) : form :=
  tuple7_formula f n k a zero zero zero r.
Lemma qpiece_record_formula_correct M rho f n k a r :
  holds M rho (qpiece_record_formula f n k a r) <->
  qpiece_record M (evalM M rho f) (evalM M rho n) (evalM M rho k) (evalM M rho a) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.
Lemma qpiece_record_total M f n k a : exists r,qpiece_record M f n k a r.
Proof. apply tuple7_total. Qed.
Lemma qpiece_record_injective M f n k a f' n' k' a' r :
  qpiece_record M f n k a r -> qpiece_record M f' n' k' a' r -> f=f' /\ n=n' /\ k=k' /\ a=a'.
Proof.
  intros H H'. destruct (tuple7_injective M f n k a _ _ _ f' n' k' a' _ _ _ r H H')
    as [HF [HN [HK [HA _]]]]. auto.
Qed.

Definition qpiece_quantifier M f a :=
  sf_relation M SFAll a (zeroM M) f \/ sf_relation M SFEx a (zeroM M) f.
Definition qpiece_quantifier_formula (f a:term) : form :=
  sf_formula SFAll a zero f ∨ sf_formula SFEx a zero f.
Definition qpiece_binary M f a b :=
  sf_relation M SFAnd a b f \/ sf_relation M SFOr a b f \/ sf_relation M SFImpl a b f.
Definition qpiece_binary_formula (f a b:term) : form :=
  sf_formula SFAnd a b f ∨ (sf_formula SFOr a b f ∨ sf_formula SFImpl a b f).
Local Opaque holds sf_formula.
Lemma qpiece_quantifier_formula_correct M rho f a :
  holds M rho (qpiece_quantifier_formula f a) <-> qpiece_quantifier M (evalM M rho f) (evalM M rho a).
Proof. unfold qpiece_quantifier_formula,qpiece_quantifier. rewrite holds_or. setoid_rewrite sf_formula_correct. reflexivity. Qed.
Lemma qpiece_binary_formula_correct M rho f a b :
  holds M rho (qpiece_binary_formula f a b) <->
  qpiece_binary M (evalM M rho f) (evalM M rho a) (evalM M rho b).
Proof. unfold qpiece_binary_formula,qpiece_binary. repeat rewrite holds_or. setoid_rewrite sf_formula_correct. reflexivity. Qed.

Definition qpiece_child M f n child childn :=
  (qpiece_quantifier M f child /\ childn=succM M n) \/
  (exists sibling,(qpiece_binary M f child sibling \/ qpiece_binary M f sibling child) /\ childn=n).
Definition qpiece_child_formula (f n child childn:term) : form :=
  (qpiece_quantifier_formula f child ∧ childn==σ n) ∨
  ∃ ((qpiece_binary_formula f`[↑] child`[↑] $0 ∨ qpiece_binary_formula f`[↑] $0 child`[↑]) ∧
    childn`[↑]==n`[↑]).
Local Opaque qpiece_quantifier_formula qpiece_binary_formula.
Lemma qpiece_child_formula_correct M rho f n child childn :
  holds M rho (qpiece_child_formula f n child childn) <->
  qpiece_child M (evalM M rho f) (evalM M rho n) (evalM M rho child) (evalM M rho childn).
Proof.
  unfold qpiece_child_formula,qpiece_child. rewrite holds_or.
  setoid_rewrite holds_ex. repeat setoid_rewrite holds_and. setoid_rewrite holds_or.
  setoid_rewrite qpiece_quantifier_formula_correct. setoid_rewrite qpiece_binary_formula_correct.
  setoid_rewrite substitution_holds_eq. setoid_rewrite substitution_map_eval_succ.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma qpiece_child_bounded M f n child childn :
  source_bounded M f n -> qpiece_child M f n child childn -> source_bounded M child childn.
Proof.
  intros HB [[[HA|HA] ->]|[sibling [[HA|HA] ->]]].
  - exact (proj1 (source_bounded_accept_unary M SFAll child f n (or_introl eq_refl) HA) HB).
  - exact (proj1 (source_bounded_accept_unary M SFEx child f n (or_intror eq_refl) HA) HB).
  - destruct HA as [HA|[HA|HA]];
      first [exact (proj1 (proj1 (source_bounded_accept_binary M SFAnd child sibling f n (or_introl eq_refl) HA) HB))
        |exact (proj1 (proj1 (source_bounded_accept_binary M SFOr child sibling f n (or_intror (or_introl eq_refl)) HA) HB))
        |exact (proj1 (proj1 (source_bounded_accept_binary M SFImpl child sibling f n (or_intror (or_intror eq_refl)) HA) HB))].
  - destruct HA as [HA|[HA|HA]];
      first [exact (proj2 (proj1 (source_bounded_accept_binary M SFAnd sibling child f n (or_introl eq_refl) HA) HB))
        |exact (proj2 (proj1 (source_bounded_accept_binary M SFOr sibling child f n (or_intror (or_introl eq_refl)) HA) HB))
        |exact (proj2 (proj1 (source_bounded_accept_binary M SFImpl sibling child f n (or_intror (or_intror eq_refl)) HA) HB))].
Qed.

Definition qpiece_base M r := exists f n a,qpiece_record M f n n a r /\ qpiece_quantifier M f a.
Definition qpiece_base_formula : form :=
  ∃∃∃ (qpiece_record_formula $2 $1 $1 $0 $3 ∧ qpiece_quantifier_formula $2 $0).
Definition qpiece_unary M r p := exists f n k a child childn,
  qpiece_record M f n k a r /\ qpiece_record M child childn k a p /\ qpiece_child M f n child childn.
Definition qpiece_lift6 (t:term) := t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Definition qpiece_unary_formula : form :=
  ∃∃∃∃∃∃ (qpiece_record_formula $5 $4 $3 $2 $6 ∧
    (qpiece_record_formula $1 $0 $3 $2 $7 ∧ qpiece_child_formula $5 $4 $1 $0)).
Local Opaque qpiece_record_formula qpiece_child_formula.
Lemma qpiece_base_formula_correct M rho r :
  holds M (r .: rho) qpiece_base_formula <-> qpiece_base M r.
Proof.
  unfold qpiece_base_formula,qpiece_base. repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite qpiece_record_formula_correct. setoid_rewrite qpiece_quantifier_formula_correct. reflexivity.
Qed.
Lemma qpiece_unary_formula_correct M rho r p :
  holds M (r .: p .: rho) qpiece_unary_formula <-> qpiece_unary M r p.
Proof.
  unfold qpiece_unary_formula,qpiece_unary. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite qpiece_record_formula_correct. setoid_rewrite qpiece_child_formula_correct. reflexivity.
Qed.

Lemma qpiece_base_bound : bounded 1 qpiece_base_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma qpiece_unary_bound : bounded 2 qpiece_unary_formula.
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Lemma qpiece_binary_bound : bounded 3 (⊥:form).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Definition qpiece_rules : NumericalRules :=
  {| rule_base_formula:=qpiece_base_formula;rule_base_bound:=qpiece_base_bound;
     rule_unary_formula:=qpiece_unary_formula;rule_unary_bound:=qpiece_unary_bound;
     rule_binary_formula:=⊥;rule_binary_bound:=qpiece_binary_bound |}.
Lemma qpiece_rule_base M r : trace_base M qpiece_rules r <-> qpiece_base M r.
Proof. apply qpiece_base_formula_correct. Qed.
Lemma qpiece_rule_unary M r p : trace_unary M qpiece_rules r p <-> qpiece_unary M r p.
Proof. apply qpiece_unary_formula_correct. Qed.
Lemma qpiece_rule_binary M r p q : trace_binary M qpiece_rules r p q -> False.
Proof. exact (fun H=>H). Qed.

Print Assumptions qpiece_child_formula_correct.
Print Assumptions qpiece_child_bounded.
Print Assumptions qpiece_base_formula_correct.
Print Assumptions qpiece_unary_formula_correct.
