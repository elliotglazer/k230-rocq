(** An actual fixed numerical instance of the WF subset rule at the two
    witness/input variables used by the uniform Separation macro. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceWFFormula NumericalWFFoundation WFSubsetCore SourceNumeralLift
  NumericalContexts NumericalSourceFull SourceProofWeakening SourceDerivedRules.
From Undecidability.FOL Require Import Syntax.Facts Deduction.FullNDFacts Sets.minZF.
From Undecidability Require Import Shared.ListAutomation.
From Stdlib Require Import Lists.List.
Import ListAutomationNotations ListAutomationHints.
Open Scope minZFsyn.
Set Implicit Arguments.
#[local] Instance wf_subset_instance_pc : peirce := class.
#[local] Hint Constructors prv : core.

Definition source_wf_subset_point : sf_form :=
  wf_class $1 → wf_subset $0 $1 → wf_class $0.

Lemma wf_subset_specialization_finite :
  (@nil sf_form) ⊢ (source_wf_subset_closed → source_wf_subset_point).
Proof.
  apply II. assert (HP:(source_wf_subset_closed :: nil) ⊢ source_wf_subset_closed)
    by (apply Ctx;cbn;auto).
  unfold source_wf_subset_closed in HP. apply (AllE $1),(AllE $0) in HP.
  wf_simp_in HP. exact HP.
Qed.

Lemma source_formula_implication_numeral M (phi psi:sf_form) :
  sf_relation M SFImpl (code_numeral M (sf_encode phi)) (code_numeral M (sf_encode psi))
    (code_numeral M (sf_encode (phi → psi))).
Proof. exact (sf_make_numeral M SFImpl (sf_encode phi) (sf_encode psi)). Qed.

Theorem numerical_wf_subset_at_witness M b c n :
  source_full_prv M b c n (source_wf_subset_code M) ->
  source_full_prv M b c n (code_numeral M (sf_encode (wf_class $1))) ->
  source_full_prv M b c n (code_numeral M (sf_encode (wf_subset $0 $1))) ->
  source_full_prv M b c n (source_wf_domain_code M).
Proof.
  intros PSubset PX PSub.
  pose proof (source_full_forward_model_empty M (source_wf_subset_closed → source_wf_subset_point)
    wf_subset_specialization_finite) as PEmpty.
  destruct (source_full_prv_wellformed M b c n (source_wf_subset_code M) PSubset) as [k [_ HC]].
  assert (PImp:source_full_prv M b c n
    (code_numeral M (sf_encode (source_wf_subset_closed → source_wf_subset_point)))).
  { apply (source_full_prv_weaken_bounded M (zeroM M) (zeroM M) (zeroM M) b c n _ k PEmpty);[|exact HC].
    intros h HH. exfalso. exact (context_empty M (zeroM M) (zeroM M) h HH). }
  pose proof (source_full_modus_ponens M b c n (source_wf_subset_code M)
    (code_numeral M (sf_encode source_wf_subset_point)) _
    (source_formula_implication_numeral M source_wf_subset_closed source_wf_subset_point)
    PImp PSubset) as PPoint.
  pose proof (source_full_modus_ponens M b c n
    (code_numeral M (sf_encode (wf_class $1)))
    (code_numeral M (sf_encode (wf_subset $0 $1 → wf_class $0))) _
    (source_formula_implication_numeral M (wf_class $1) (wf_subset $0 $1 → wf_class $0))
    PPoint PX) as PLast.
  exact (source_full_modus_ponens M b c n
    (code_numeral M (sf_encode (wf_subset $0 $1))) (source_wf_domain_code M) _
    (source_formula_implication_numeral M (wf_subset $0 $1) (wf_class $0)) PLast PSub).
Qed.

Print Assumptions wf_subset_specialization_finite.
Print Assumptions numerical_wf_subset_at_witness.
