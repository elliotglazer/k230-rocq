(** Actual raw-membership introduction, uniformly at model-valued names. *)
From CollectionRaw Require Import RawMembershipIntroCertificate.
From PAModel Require Import Model FiniteCoding CodeDescent CodeExpressions NumericalProofs NamedLeibnizSteps
  NumericalEquivalence ProofTemplates QuotientAtomTemplates QuotationPayloads
  OldNamedSyntaxBridge ZFCFiniteAxiomTemplates FiniteRawPrefixCertificate RawLawGraphs RawLawConsequences.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia Lists.List.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition member_intro_body := isolated_formula raw_member_intro_body.
Definition member_intro_parameters M (k t x y:carrier M) := k .: t .: x .: y .: fun _=>zeroM M.
Definition member_intro_environment := CEvar 3 .: CEvar 2 .: CEvar 1 .: fun _=>CEconst 0.
Definition member_intro_values M (t x y:carrier M) := y .: x .: t .: fun _=>zeroM M.

Lemma member_intro_closed : bounded 0 (isolated_formula raw_member_intro_source).
Proof. apply set_formula_boundb_sound;vm_compute;reflexivity. Qed.

Lemma member_intro_body_template M k t x y :
  coding_lt M (zeroM M) k -> coding_lt M t k -> coding_lt M x k -> coding_lt M y k ->
  ns_proof M (member_intro_parameters M k t x y)
    (template_set_formula member_intro_environment (CEvar 0) member_intro_body).
Proof.
  intros H0 Ht Hx Hy.
  apply (finite_original_prefix_instance M raw_member_intro_body 3
    (cons (CEvar 1) (cons (CEvar 2) (cons (CEvar 3) nil)))
    (member_intro_parameters M k t x y) (CEvar 0) k (member_intro_values M t x y)).
  - exact member_intro_closed.
  - exact original_raw_member_intro_certificate.
  - reflexivity.
  - reflexivity.
  - exact H0.
  - intros [|[|[|i]]];reflexivity.
  - intros [|[|[|i]]];assumption.
  - intros arg [<-|[<-|[<-|[]]]].
    + exists t;split;[reflexivity|exact Ht].
    + exists x;split;[reflexivity|exact Hx].
    + exists y;split;[reflexivity|exact Hy].
Qed.

Lemma member_intro_body_expression :
  template_set_formula member_intro_environment (CEvar 0) member_intro_body =
  E_wim (raw_marker_expression (CEvar 1) (CEvar 0))
    (E_wim (E_wel (CEvar 1) (CEvar 2))
      (E_wim (E_wel (CEvar 2) (CEvar 3))
        (raw_atom_expression false (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 0)))).
Proof. reflexivity. Qed.

Theorem actual_raw_membership_intro M t name marker x y k dom mem q h :
  coding_lt M (zeroM M) name -> coding_lt M t name -> raw_marker_at M t name marker ->
  coding_lt M (zeroM M) k -> coding_lt M t k -> coding_lt M x k -> coding_lt M y k ->
  membership_graph M t x dom -> membership_graph M x y mem ->
  quotation_atom M false x y t k q ->
  code_relation M (dom .: mem .: q .: fun _=>zeroM M)
    (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) h ->
  numerical_implies M marker h.
Proof.
  intros HN HTN HM HK HT HX HY HD HMem HQ HH.
  set (rho:=member_intro_parameters M k t x y).
  destruct (code_relation_total M (raw_marker_expression (CEvar 1) (CEvar 0)) rho) as [mk Hmk].
  assert (HMK : raw_marker_at M t k mk).
  { exact (proj1 (raw_marker_expression_graph M rho (CEvar 1) (CEvar 0) t k mk eq_refl eq_refl) Hmk). }
  assert (GD : code_relation M rho (E_wel (CEvar 1) (CEvar 2)) dom).
  { exact (proj2 (ns_atom_expression M rho false (CEvar 1) (CEvar 2) t x dom eq_refl eq_refl) HD). }
  assert (GM : code_relation M rho (E_wel (CEvar 2) (CEvar 3)) mem).
  { exact (proj2 (ns_atom_expression M rho false (CEvar 2) (CEvar 3) x y mem eq_refl eq_refl) HMem). }
  assert (GQ : code_relation M rho (raw_atom_expression false (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 0)) q).
  { exact (proj2 (raw_atom_expression_graph M rho false (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 0)
      t x y k q eq_refl eq_refl eq_refl eq_refl) HQ). }
  assert (GH : code_relation M rho (E_wim (E_wel (CEvar 1) (CEvar 2))
    (E_wim (E_wel (CEvar 2) (CEvar 3))
      (raw_atom_expression false (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 0)))) h).
  { exact (raw_binary_expression_graph M rho _ _ _ dom mem q h GD GM GQ HH). }
  apply (numerical_implies_trans M marker mk h).
  - exact (proj1 (raw_marker_rebase M t name k marker mk HN HTN HK HT HM HMK)).
  - apply (proj1 (numerical_implies_expression M rho (raw_marker_expression (CEvar 1) (CEvar 0)) _ mk h Hmk GH)).
    rewrite <-member_intro_body_expression. exact (member_intro_body_template M k t x y HK HT HX HY).
Qed.

Print Assumptions member_intro_body_template.
Print Assumptions actual_raw_membership_intro.
