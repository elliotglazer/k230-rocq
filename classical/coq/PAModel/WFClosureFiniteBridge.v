(** The fixed old minimal WF closure derivation is an actual current source
    proof, and therefore an actual numerical proof in every PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge SourceWFFormula SourceNumeralLift
  SourceFiniteContexts NumericalContexts NumericalSourceFull.
From PAModel Require OldWFFiniteClosure.
From OldRegCon Require MinZF.
From Undecidability.FOL Require Import Syntax.Core Sets.minZF Deduction.FullND.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lists.List.
Open Scope minZFsyn.
Unset Implicit Arguments.

Definition source_wf_closure : sf_form :=
  ∀((∀($0 ∈' $1 → wf_class $0)) → wf_class $0).
Definition source_wf_closure_code M := code_numeral M (sf_encode source_wf_closure).

Lemma old_wf_domain_source_exact :
  isolated_formula OldWFFiniteClosure.old_wf_domain=wf_domain.
Proof. reflexivity. Qed.
Lemma old_wf_closure_source_exact :
  isolated_formula OldWFFiniteClosure.old_wf_closure=source_wf_closure.
Proof. reflexivity. Qed.

Theorem source_wf_closure_finite :
  exists A:list (isolated_old_form OC.falsity_on),
    (forall a,In a A -> OldRegCon.MinZF.ZFcl_min a) /\
    @Undecidability.FOL.Deduction.FullND.prv
      Undecidability.FOL.Syntax.BinSig.sig_empty
      Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
      Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.class
      (List.map isolated_formula A) source_wf_closure.
Proof.
  destruct OldWFFiniteClosure.old_minimal_wf_closure as [A [HA HP]].
  exists A. split;[exact HA|]. rewrite <-old_wf_closure_source_exact.
  exact (@isolated_fullnd_to_current OC.falsity_on OC.class A
    OldWFFiniteClosure.old_wf_closure HP).
Qed.

Theorem numerical_wf_closure_finite_context M :
  exists A b c n,
    (forall a,In a A -> OldRegCon.MinZF.ZFcl_min a) /\
    source_model_context_represents M b c n (List.map isolated_formula A) /\
    source_full_prv M b c n (source_wf_closure_code M).
Proof.
  destruct source_wf_closure_finite as [A [HA HP]].
  destruct (source_model_context_total M (List.map isolated_formula A)) as [b [c [n HC]]].
  exists A,b,c,n. split;[exact HA|]. split;[exact HC|].
  exact (@source_full_forward_model Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.class M
    (List.map isolated_formula A) source_wf_closure HP b c n HC).
Qed.

Print Assumptions old_wf_domain_source_exact.
Print Assumptions source_wf_closure_finite.
Print Assumptions numerical_wf_closure_finite_context.
