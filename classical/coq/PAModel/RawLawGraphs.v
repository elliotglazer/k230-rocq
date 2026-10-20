(** Exact graph interfaces for raw marker and quotient atom law templates. *)
From RawLogic Require Import RawLogicCertificates.
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates
  NumericalEquivalence RawLawTemplates RawLawInstances QuotientAtomTemplates
  QuotationPayloads FiniteTemplateEvaluation FiniteTemplateRebase.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.

Definition raw_marker_expression t k := E_wal k (E_wn (E_wel k t)).
Definition raw_marker_at M t k marker :=
  code_relation M (t .: k .: fun _=>zeroM M)
    (raw_marker_expression (CEvar 0) (CEvar 1)) marker.
Definition raw_atom_expression equality t x y k :=
  code_subst (quotation_atom_parameters x y t k (CEconst 0)) (quotation_atom_expression equality).

Definition raw_law_expression law :=
  let marker := raw_marker_expression (CEvar 1) (CEvar 0) in
  let atom := fun equality x y => raw_atom_expression equality (CEvar 1) x y (CEvar 0) in
  match law with
  | RawSymmetry => E_wim marker (E_wim (atom true (CEvar 2) (CEvar 3)) (atom true (CEvar 3) (CEvar 2)))
  | RawTransitivity => E_wim marker (E_wim (atom true (CEvar 2) (CEvar 3))
      (E_wim (atom true (CEvar 3) (CEvar 4)) (atom true (CEvar 2) (CEvar 4))))
  | RawLeft => E_wim marker (E_wim (atom true (CEvar 2) (CEvar 3))
      (E_wim (atom false (CEvar 2) (CEvar 4)) (atom false (CEvar 3) (CEvar 4))))
  | RawRight => E_wim marker (E_wim (atom true (CEvar 3) (CEvar 4))
      (E_wim (atom false (CEvar 2) (CEvar 3)) (atom false (CEvar 2) (CEvar 4))))
  end.

Lemma raw_law_expression_exact law :
  template_set_formula (raw_body_environment law) (CEvar 0) (current_raw_body law) =
  raw_law_expression law.
Proof. destruct law;reflexivity. Qed.

Lemma raw_marker_expression_graph M rho T K t k marker :
  code_relation M rho T t -> code_relation M rho K k ->
  (code_relation M rho (raw_marker_expression T K) marker <-> raw_marker_at M t k marker).
Proof.
  intros HT HK.
  change (code_relation M rho
    (code_subst (T .: K .: fun _=>CEconst 0)
      (raw_marker_expression (CEvar 0) (CEvar 1))) marker <->
    code_relation M (t .: k .: fun _=>zeroM M)
      (raw_marker_expression (CEvar 0) (CEvar 1)) marker).
  apply code_subst_graph. intros [|[|idx]];[exact HT|exact HK|reflexivity].
Qed.

Lemma raw_atom_expression_graph M rho equality T X Y K t x y k f :
  code_relation M rho T t -> code_relation M rho X x ->
  code_relation M rho Y y -> code_relation M rho K k ->
  (code_relation M rho (raw_atom_expression equality T X Y K) f <-> quotation_atom M equality x y t k f).
Proof.
  intros HT HX HY HK. unfold raw_atom_expression,quotation_atom.
  apply code_subst_graph. intros [|[|[|[|idx]]]];[exact HX|exact HY|exact HT|exact HK|reflexivity].
Qed.

Definition raw_marker_source : set_form := ∀ ($0 ∈' $1 → ⊥).
Lemma raw_marker_evaluation M t k marker :
  raw_marker_at M t k marker ->
  template_evaluation M raw_marker_source (fun _=>t) k marker.
Proof.
  intro HM. apply (proj1 (template_evaluation_graph M raw_marker_source
    (fun _=>CEvar 0) (CEvar 1) (t .: k .: fun _=>zeroM M)
    (fun _=>t) k marker ltac:(intro;reflexivity) eq_refl)). exact HM.
Qed.

Theorem raw_marker_rebase M t k l a b :
  coding_lt M (zeroM M) k -> coding_lt M t k ->
  coding_lt M (zeroM M) l -> coding_lt M t l ->
  raw_marker_at M t k a -> raw_marker_at M t l b -> numerical_equivalent M a b.
Proof.
  intros Hk0 Hkt Hl0 Hlt HA HB.
  exact (finite_template_rebase M raw_marker_source (fun _=>t) k l a b
    (template_hygienic_below M raw_marker_source (fun _=>t) k Hk0 (fun _=>Hkt))
    (template_hygienic_below M raw_marker_source (fun _=>t) l Hl0 (fun _=>Hlt))
    (raw_marker_evaluation M t k a HA) (raw_marker_evaluation M t l b HB)).
Qed.

Print Assumptions raw_law_expression_exact.
Print Assumptions raw_marker_expression_graph.
Print Assumptions raw_atom_expression_graph.
Print Assumptions raw_marker_rebase.
