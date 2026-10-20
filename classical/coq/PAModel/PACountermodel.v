From Undecidability.FOL.Arithmetics Require Import Signature.
From FOL.Completeness Require Import TarskiCompleteness.

Module CountermodelFragment := Undecidability.FOL.Semantics.Tarski.FragmentCore.
Module CountermodelFacts := Undecidability.FOL.Semantics.Tarski.FragmentFacts.
Module CountermodelND := Undecidability.FOL.Deduction.FragmentND.
Module CountermodelNDFacts := Undecidability.FOL.Deduction.FragmentNDFacts.
Module CountermodelTheory := Undecidability.FOL.Syntax.Theories.

Definition pa_fragment_formula :=
  @form PA_funcs_signature PA_preds_signature FragmentSyntax.frag_operators falsity_on.
Definition pa_fragment_theory := pa_fragment_formula -> Prop.
Definition pa_fragment_negation (phi : pa_fragment_formula) : pa_fragment_formula :=
  @bin PA_funcs_signature PA_preds_signature FragmentSyntax.frag_operators falsity_on FragmentSyntax.Impl phi falsity.

(** The model is the pinned syntactic Henkin model on the original arithmetic
    term type.  Closure is used explicitly to promote validity at [var] to
    validity at every valuation; no completeness principle is a premise. *)
Theorem pa_closed_fragment_term_countermodel
    (T : pa_fragment_theory) (theta : pa_fragment_formula)
    (HT : CountermodelTheory.closed_T T) (Htheta : closed theta)
    (Hnot : ~ @CountermodelND.tprv PA_funcs_signature PA_preds_signature falsity_on class T theta) :
  exists I : @CountermodelFragment.interp PA_funcs_signature PA_preds_signature
      (@term PA_funcs_signature),
    @CountermodelFragment.classical PA_funcs_signature PA_preds_signature
      falsity_on (@term PA_funcs_signature) I /\
    (forall phi rho, T phi -> @CountermodelFragment.sat
      PA_funcs_signature PA_preds_signature (@term PA_funcs_signature)
      I falsity_on rho phi) /\
    @CountermodelFragment.sat PA_funcs_signature PA_preds_signature
      (@term PA_funcs_signature) I falsity_on var (pa_fragment_negation theta).
Proof.
  assert (Hclosed : CountermodelTheory.closed_T
      (CountermodelTheory.extend T (pa_fragment_negation theta))).
  { apply CountermodelTheory.closed_T_extend; [exact HT|].
    unfold pa_fragment_negation. constructor; [exact Htheta|constructor]. }
  assert (Hconsistent : @CountermodelND.consistent PA_funcs_signature PA_preds_signature class
      (CountermodelTheory.extend T (pa_fragment_negation theta))).
  { intros Hbot. apply Hnot.
    exact (proj2 (@CountermodelNDFacts.refutation_prv
      PA_funcs_signature PA_preds_signature PA_funcs_eq PA_preds_eq T theta) Hbot). }
  exists (@model_bot PA_funcs_signature PA_preds_signature PA_funcs_eq PA_preds_eq
    enum_PA_funcs enumerator_PA_funcs enum_PA_preds enumerator_PA_preds
    (CountermodelTheory.extend T (pa_fragment_negation theta)) Hclosed).
  split.
  - exact (@model_bot_classical PA_funcs_signature PA_preds_signature
      PA_funcs_eq PA_preds_eq enum_PA_funcs enumerator_PA_funcs
      enum_PA_preds enumerator_PA_preds _ Hclosed Hconsistent).
  - split.
    + intros phi rho Hphi.
      apply (proj1 (@CountermodelFacts.sat_closed PA_funcs_signature
        PA_preds_signature (@term PA_funcs_signature) _ falsity_on var rho phi
        (HT phi Hphi))).
      apply (@valid_T_model_bot PA_funcs_signature PA_preds_signature
        PA_funcs_eq PA_preds_eq enum_PA_funcs enumerator_PA_funcs
        enum_PA_preds enumerator_PA_preds _ Hclosed Hconsistent phi).
      now left.
    + apply (@valid_T_model_bot PA_funcs_signature PA_preds_signature
        PA_funcs_eq PA_preds_eq enum_PA_funcs enumerator_PA_funcs
        enum_PA_preds enumerator_PA_preds _ Hclosed Hconsistent
        (pa_fragment_negation theta)).
      now right.
Qed.

Corollary pa_closed_fragment_term_countermodel_not
    (T : pa_fragment_theory) (theta : pa_fragment_formula)
    (HT : CountermodelTheory.closed_T T) (Htheta : closed theta)
    (Hnot : ~ @CountermodelND.tprv PA_funcs_signature PA_preds_signature falsity_on class T theta) :
  exists I : @CountermodelFragment.interp PA_funcs_signature PA_preds_signature
      (@term PA_funcs_signature),
    (forall phi rho, T phi -> @CountermodelFragment.sat
      PA_funcs_signature PA_preds_signature (@term PA_funcs_signature)
      I falsity_on rho phi) /\
    ~ @CountermodelFragment.sat PA_funcs_signature PA_preds_signature
      (@term PA_funcs_signature) I falsity_on var theta.
Proof.
  destruct (@pa_closed_fragment_term_countermodel T theta HT Htheta Hnot)
    as [I [HI [HTI Hneg]]].
  exists I. split; [exact HTI|exact Hneg].
Qed.

Print Assumptions pa_closed_fragment_term_countermodel.
Print Assumptions pa_closed_fragment_term_countermodel_not.



