(** Actual fixed instance of WF closure at the Replacement output witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceWFFormula NumericalWFFoundation WFClosureFiniteBridge SourceNumeralLift
  NumericalContexts NumericalSourceFull SourceProofWeakening SourceDerivedRules
  WFSubsetInstantiation.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lists.List.
Import ListAutomationNotations ListAutomationHints.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance wf_closure_instance_pc : peirce := class.
#[local] Hint Constructors prv : core.

Definition source_wf_members : sf_form := ∀($0 ∈' $1 → wf_class $0).
Definition source_wf_closure_point : sf_form := source_wf_members → wf_class $0.
Definition source_wf_members_code M := code_numeral M (sf_encode source_wf_members).

Lemma wf_closure_specialization_finite :
  (@nil sf_form) ⊢ (source_wf_closure → source_wf_closure_point).
Proof.
  apply II. assert (HP:(source_wf_closure :: nil) ⊢ source_wf_closure)
    by (apply Ctx;cbn;auto).
  unfold source_wf_closure in HP. apply (AllE $0) in HP.
  wf_simp_in HP. exact HP.
Qed.

Theorem numerical_wf_closure_at_witness M b c n :
  source_full_prv M b c n (source_wf_closure_code M) ->
  source_full_prv M b c n (source_wf_members_code M) ->
  source_full_prv M b c n (source_wf_domain_code M).
Proof.
  intros PClosure PMembers.
  pose proof (source_full_forward_model_empty M (source_wf_closure → source_wf_closure_point)
    wf_closure_specialization_finite) as PEmpty.
  destruct (source_full_prv_wellformed M b c n (source_wf_closure_code M) PClosure) as [k [_ HC]].
  assert (PImp:source_full_prv M b c n
    (code_numeral M (sf_encode (source_wf_closure → source_wf_closure_point)))).
  { apply (source_full_prv_weaken_bounded M (zeroM M) (zeroM M) (zeroM M) b c n _ k PEmpty);[|exact HC].
    intros h HH. exfalso. exact (context_empty M (zeroM M) (zeroM M) h HH). }
  pose proof (source_full_modus_ponens M b c n (source_wf_closure_code M)
    (code_numeral M (sf_encode source_wf_closure_point)) _
    (source_formula_implication_numeral M source_wf_closure source_wf_closure_point)
    PImp PClosure) as PPoint.
  exact (source_full_modus_ponens M b c n (source_wf_members_code M) (source_wf_domain_code M) _
    (source_formula_implication_numeral M source_wf_members (wf_class $0)) PPoint PMembers).
Qed.

Print Assumptions wf_closure_specialization_finite.
Print Assumptions numerical_wf_closure_at_witness.
