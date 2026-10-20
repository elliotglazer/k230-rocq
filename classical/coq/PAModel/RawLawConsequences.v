(** Numerical consequences of the actual finite KLogic certificates. *)
From RawLogic Require Import RawLogicCertificates.
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  NumericalVacuitySteps ProofTemplates NumericalEquivalence
  RawLawTemplates RawLawInstances RawLawGraphs QuotientAtomTemplates QuotationPayloads.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition raw_consequence_expression law :=
  let atom := fun equality x y => raw_atom_expression equality (CEvar 1) x y (CEvar 0) in
  match law with
  | RawSymmetry => E_wim (atom true (CEvar 2) (CEvar 3)) (atom true (CEvar 3) (CEvar 2))
  | RawTransitivity => E_wim (atom true (CEvar 2) (CEvar 3))
      (E_wim (atom true (CEvar 3) (CEvar 4)) (atom true (CEvar 2) (CEvar 4)))
  | RawLeft => E_wim (atom true (CEvar 2) (CEvar 3))
      (E_wim (atom false (CEvar 2) (CEvar 4)) (atom false (CEvar 3) (CEvar 4)))
  | RawRight => E_wim (atom true (CEvar 3) (CEvar 4))
      (E_wim (atom false (CEvar 2) (CEvar 3)) (atom false (CEvar 2) (CEvar 4)))
  end.

Lemma raw_law_consequence_exact law :
  raw_law_expression law = E_wim (raw_marker_expression (CEvar 1) (CEvar 0))
    (raw_consequence_expression law).
Proof. destruct law;reflexivity. Qed.

Theorem raw_certificate_consequence law M k t x y z name marker h :
  coding_lt M (zeroM M) k -> coding_lt M t k ->
  coding_lt M x k -> coding_lt M y k -> coding_lt M z k ->
  coding_lt M (zeroM M) name -> coding_lt M t name ->
  raw_marker_at M t name marker ->
  code_relation M (raw_parameters M k t x y z) (raw_consequence_expression law) h ->
  numerical_implies M marker h.
Proof.
  intros HK HT HX HY HZ HN HTN HM HH.
  set (rho:=raw_parameters M k t x y z).
  destruct (code_relation_total M (raw_marker_expression (CEvar 1) (CEvar 0)) rho)
    as [mk Hmk].
  assert (HMK : raw_marker_at M t k mk).
  { apply (proj1 (raw_marker_expression_graph M rho (CEvar 1) (CEvar 0) t k mk
      eq_refl eq_refl));exact Hmk. }
  apply (numerical_implies_trans M marker mk h).
  - exact (proj1 (raw_marker_rebase M t name k marker mk HN HTN HK HT HM HMK)).
  - apply (proj1 (numerical_implies_expression M rho
      (raw_marker_expression (CEvar 1) (CEvar 0)) (raw_consequence_expression law)
      mk h Hmk HH)).
    rewrite <-raw_law_consequence_exact, <-raw_law_expression_exact.
    exact (raw_body_template_proved law M k t x y z HK HT HX HY HZ).
Qed.

Lemma raw_implication_expression_graph M rho A B a b h :
  code_relation M rho A a -> code_relation M rho B b ->
  implication_graph M a b h -> code_relation M rho (E_wim A B) h.
Proof. intros HA HB HH;exact (proj2 (expression_implication_iff M rho A B a b h HA HB) HH). Qed.

Lemma raw_binary_expression_graph M rho A B C a b c h :
  code_relation M rho A a -> code_relation M rho B b -> code_relation M rho C c ->
  code_relation M (a .: b .: c .: fun _=>zeroM M)
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) h ->
  code_relation M rho (E_wim A (E_wim B C)) h.
Proof.
  intros HA HB HC HH.
  change (code_relation M rho (code_subst (A .: B .: C .: fun _=>CEconst 0)
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2)))) h).
  apply (proj2 (code_subst_graph M rho (A .: B .: C .: fun _=>CEconst 0)
    (a .: b .: c .: fun _=>zeroM M)
    ltac:(intros [|[|[|idx]]];[exact HA|exact HB|exact HC|reflexivity])
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) h)).
  exact HH.
Qed.

Print Assumptions raw_certificate_consequence.
Print Assumptions raw_implication_expression_graph.
Print Assumptions raw_binary_expression_graph.
