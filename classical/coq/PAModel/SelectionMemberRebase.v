(** Replace the common representative allocation by the allocation used
    in the canonical source image. These are genuine numerical proof
    equivalences and remain valid under the outer quantifiers. *)
From PAModel Require Import Model CodeExpressions ProofTemplates NumericalEquivalence
  QuotientAtomTemplates QuotationPayloads SupportedQuotientEnvironments RawQuotientAtomCongruence
  QuotientMemberExpansion QuotientSeparationWitness LiteralMemberSeparationPoint QuotedSameContainer.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_member_at T X Y K :=
  code_subst (quotation_atom_parameters X Y T K (CEconst 0)) quotient_member_template.
Definition E_selection_at T X A C K Q :=
  E_selection_iff (E_member_at T X C K) (E_wa (E_member_at T X A K) Q).
Definition E_selection_container_at T X A C K Q :=
  E_wa (E_wel T C) (E_wal X (E_wim (E_wel T X) (E_selection_at T X A C K Q))).

Lemma member_at_graph M env T X Y K t x y k out :
  code_relation M env T t -> code_relation M env X x ->
  code_relation M env Y y -> code_relation M env K k ->
  (code_relation M env (E_member_at T X Y K) out <-> quotation_atom M false x y t k out).
Proof.
  intros HT HX HY HK. unfold E_member_at,quotation_atom,quotation_atom_expression.
  apply code_subst_graph. intros [|[|[|[|i]]]];[exact HX|exact HY|exact HT|exact HK|reflexivity].
Qed.

Lemma member_expression_rebase M env T X Y W K t x y w k :
  code_relation M env T t -> code_relation M env X x -> code_relation M env Y y ->
  code_relation M env W w -> code_relation M env K k ->
  quotient_pair_safe M t x y w -> quotient_pair_safe M t x y k ->
  expression_equivalent M env (E_member_witness T X Y W) (E_member_at T X Y K).
Proof.
  intros HT HX HY HW HK HWS HKS.
  destruct (code_relation_total M (E_member_witness T X Y W) env) as [left HL].
  destruct (code_relation_total M (E_member_at T X Y K) env) as [right HR].
  apply (proj2 (numerical_equivalent_expression M env _ _ left right HL HR)).
  apply (raw_atom_rebase M false t x y w k left right HWS HKS).
  - exact (proj1 (member_witness_atom_graph M env T X Y W t x y w left HT HX HY HW) HL).
  - exact (proj1 (member_at_graph M env T X Y K t x y k right HT HX HY HK) HR).
Qed.

Lemma selection_iff_congruence M env P P' Q Q' :
  expression_equivalent M env P P' -> expression_equivalent M env Q Q' ->
  expression_equivalent M env (E_selection_iff P Q) (E_selection_iff P' Q').
Proof.
  intros HP HQ. unfold E_selection_iff.
  apply expression_equivalent_conjunction;apply expression_equivalent_implication;assumption.
Qed.

Theorem selection_member_rebase M env T X A C W K Q t x a c w k :
  code_relation M env T t -> code_relation M env X x -> code_relation M env A a ->
  code_relation M env C c -> code_relation M env W w -> code_relation M env K k ->
  quotient_pair_safe M t x a w -> quotient_pair_safe M t x a k ->
  quotient_pair_safe M t x c w -> quotient_pair_safe M t x c k ->
  expression_equivalent M env (E_literal_member_selection T X A C W Q) (E_selection_at T X A C K Q).
Proof.
  intros HT HX HA HC HW HK HWa HKa HWc HKc.
  apply selection_iff_congruence.
  - exact (member_expression_rebase M env T X C W K t x c w k HT HX HC HW HK HWc HKc).
  - apply expression_equivalent_conjunction;[|apply expression_equivalent_refl].
    exact (member_expression_rebase M env T X A W K t x a w k HT HX HA HW HK HWa HKa).
Qed.

Theorem selection_container_rebase M env T X A C W K Q t x a c w k :
  code_relation M env T t -> code_relation M env X x -> code_relation M env A a ->
  code_relation M env C c -> code_relation M env W w -> code_relation M env K k ->
  quotient_pair_safe M t x a w -> quotient_pair_safe M t x a k ->
  quotient_pair_safe M t x c w -> quotient_pair_safe M t x c k ->
  expression_equivalent M env
    (E_wex C (E_quotient_selection_container T X A C W Q))
    (E_wex C (E_selection_container_at T X A C K Q)).
Proof.
  intros HT HX HA HC HW HK HWa HKa HWc HKc.
  apply expression_equivalent_exists.
  apply expression_equivalent_conjunction;[apply expression_equivalent_refl|].
  apply expression_equivalent_all,expression_equivalent_implication;[apply expression_equivalent_refl|].
  exact (selection_member_rebase M env T X A C W K Q t x a c w k HT HX HA HC HW HK HWa HKa HWc HKc).
Qed.

Print Assumptions member_expression_rebase.
Print Assumptions selection_container_rebase.
