(** A fixed useful derived rule for the uniform WF Separation proof:
    every subset of a WF set is WF. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge SourceWFFormula WFClosureFiniteBridge OldWFCoreCorrespondence
  NumericalWFCoreFixed CoreConsistencyReduction NumericalCoreAxioms.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lists.List.
Import ListAutomationNotations ListAutomationHints.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance wf_subset_pc : peirce := class.
#[local] Hint Constructors prv : core.

Definition source_wf_subset_closed : sf_form :=
  ∀∀(wf_class $1 → wf_subset $0 $1 → wf_class $0).
Definition source_wf_subset_code M := code_numeral M (sf_encode source_wf_subset_closed).

Lemma wf_source_subset_closed_prv (G:list sf_form) :
  In source_wf_closure G -> G ⊢ source_wf_subset_closed.
Proof.
  intro HClosure. unfold source_wf_subset_closed.
  apply AllI_named. intros x. wf_simp.
  apply AllI_named. intros y. wf_simp. apply II,II.
  assert (HP:(wf_subset y x :: wf_class x :: G) ⊢ source_wf_closure)
    by (apply Ctx;cbn;tauto).
  unfold source_wf_closure in HP. apply (AllE y) in HP. wf_simp_in HP.
  eapply IE;[exact HP|]. apply AllI_named. intros z. wf_simp. apply II.
  eapply wf_source_member with (x:=x) (y:=z).
  - apply Ctx;cbn;tauto.
  - eapply wf_source_subset_elim with (x:=y) (y:=x) (z:=z);apply Ctx;cbn;tauto.
Qed.

Theorem source_wf_subset_finite :
  exists A:list sf_form,(forall a,In a A -> standard_zfc_core_source_axiom a) /\
    A ⊢ source_wf_subset_closed.
Proof.
  destruct source_wf_closure_finite as [A [HA HP]].
  exists (List.map isolated_formula A). split.
  - intros a HIn. apply List.in_map_iff in HIn. destruct HIn as [olda [<- HIn]].
    apply old_wf_minimal_core_exact,HA,HIn.
  - apply (prv_cut (wf_source_subset_closed_prv (G:=source_wf_closure :: List.map isolated_formula A)
      (or_introl eq_refl))).
    intros a [<-|HIn];[exact HP|apply Ctx;exact HIn].
Qed.

Theorem numerical_wf_subset_core M : source_core_provable M (source_wf_subset_code M).
Proof.
  destruct source_wf_subset_finite as [A [HA HP]].
  exact (finite_current_core_proof_lift M A source_wf_subset_closed HA HP).
Qed.

Print Assumptions wf_source_subset_closed_prv.
Print Assumptions source_wf_subset_finite.
Print Assumptions numerical_wf_subset_core.
