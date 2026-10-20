(** Arithmetic recognition of closed source ZFC axiom instances.
    This is a predicate on eight-tag SOURCE formula codes, not the target
    Hilbert calculus and not a proof-preservation theorem.

    The input bound and a final closedness check are both explicit.  Their
    redundancy is not assumed here.  Every quantified code, length, and
    witness below ranges over the arbitrary PA model's carrier. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs SentenceBounds SetFormulaCodes SourceBounded
  SchemaRenamingDescriptors SetSchemaConstructors NumericalSetClosure
  ZFCFiniteSourceCodes.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_separation_instance M phi n z :=
  source_bounded M phi (succM M n) /\
  exists body open_code,
    schema_renaming M SepBody phi body /\
    sf_separation_constructor M body open_code /\
    all_prefix M n open_code z.
Definition numerical_replacement_instance M phi n z :=
  source_bounded M phi (succM M (succM M n)) /\
  exists bodyA bodyB bodyC open_code,
    schema_renaming M RepA phi bodyA /\
    schema_renaming M RepB phi bodyB /\
    schema_renaming M RepC phi bodyC /\
    sf_replacement_constructor M bodyA bodyB bodyC open_code /\
    all_prefix M n open_code z.

Definition numerical_closed_separation M z :=
  source_bounded M z (zeroM M) /\ exists phi n, numerical_separation_instance M phi n z.
Definition numerical_closed_replacement M z :=
  source_bounded M z (zeroM M) /\ exists phi n, numerical_replacement_instance M phi n z.

(** Quantifier slots in the first formula are open,body,n,phi. *)
Definition numerical_closed_separation_formula (z : pa_term) : pa_form :=
  source_bounded_accept_formula z zero ∧
  ∃∃∃∃ (source_bounded_accept_formula $3 (σ $2) ∧
    (schema_renaming_formula SepBody $3 $1 ∧
    (sf_separation_constructor_formula $1 $0 ∧ all_prefix_formula $2 $0 (lift4 z)))).

Definition zfc_lift6 (t : pa_term) := t`[↑]`[↑]`[↑]`[↑]`[↑]`[↑].
Lemma zfc_eval_lift6 M rho a b c d e f t :
  evalM M (f .: e .: d .: c .: b .: a .: rho) (zfc_lift6 t)=evalM M rho t.
Proof. unfold evalM,zfc_lift6. now rewrite !eval_up. Qed.

(** Quantifier slots are open,C,B,A,n,phi. *)
Definition numerical_closed_replacement_formula (z : pa_term) : pa_form :=
  source_bounded_accept_formula z zero ∧
  ∃∃∃∃∃∃ (source_bounded_accept_formula $5 (σ (σ $4)) ∧
    (schema_renaming_formula RepA $5 $3 ∧
    (schema_renaming_formula RepB $5 $2 ∧
    (schema_renaming_formula RepC $5 $1 ∧
    (sf_replacement_constructor_formula $3 $2 $1 $0 ∧
    all_prefix_formula $4 $0 (zfc_lift6 z)))))).

Local Opaque holds source_bounded_accept_formula schema_renaming_formula
  sf_separation_constructor_formula sf_replacement_constructor_formula all_prefix_formula.

Theorem numerical_closed_separation_formula_correct M rho z :
  holds M rho (numerical_closed_separation_formula z) <->
  numerical_closed_separation M (evalM M rho z).
Proof.
  unfold numerical_closed_separation_formula,numerical_closed_separation,
    numerical_separation_instance.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite schema_renaming_formula_correct.
  setoid_rewrite sf_separation_constructor_correct.
  setoid_rewrite all_prefix_formula_correct. try setoid_rewrite lift4_correct.
  split.
  - intros [Hclosed [phi [n [body [open_code [Hbound H]]]]]].
    split; [exact Hclosed|]. exists phi,n. split; [exact Hbound|]. now exists body,open_code.
  - intros [Hclosed [phi [n [Hbound [body [open_code H]]]]]].
    split; [exact Hclosed|]. exists phi,n,body,open_code. auto.
Qed.

Theorem numerical_closed_replacement_formula_correct M rho z :
  holds M rho (numerical_closed_replacement_formula z) <->
  numerical_closed_replacement M (evalM M rho z).
Proof.
  unfold numerical_closed_replacement_formula,numerical_closed_replacement,
    numerical_replacement_instance.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite schema_renaming_formula_correct.
  setoid_rewrite sf_replacement_constructor_correct.
  setoid_rewrite all_prefix_formula_correct. try setoid_rewrite zfc_eval_lift6.
  split.
  - intros [Hclosed [phi [n [a [b [c [open_code [Hbound H]]]]]]]].
    split; [exact Hclosed|]. exists phi,n. split; [exact Hbound|]. now exists a,b,c,open_code.
  - intros [Hclosed [phi [n [Hbound [a [b [c [open_code H]]]]]]]].
    split; [exact Hclosed|]. exists phi,n,a,b,c,open_code. auto.
Qed.

(** The fixed branch contains exactly the twelve tags listed by the pinned
    ZFCFiniteSourceCodes module. No NumericalTheory wrapper is introduced. *)
Definition numerical_zfc_source_axiom M z :=
  (exists tag, zfc_source_graph M tag z) \/
  numerical_closed_separation M z \/ numerical_closed_replacement M z.
Definition numerical_zfc_source_axiom_formula (z : pa_term) : pa_form :=
  zfc_fixed_source_formula z ∨
  (numerical_closed_separation_formula z ∨ numerical_closed_replacement_formula z).

Local Opaque zfc_fixed_source_formula numerical_closed_separation_formula
  numerical_closed_replacement_formula.
Theorem numerical_zfc_source_axiom_formula_correct M rho z :
  holds M rho (numerical_zfc_source_axiom_formula z) <->
  numerical_zfc_source_axiom M (evalM M rho z).
Proof.
  unfold numerical_zfc_source_axiom_formula,numerical_zfc_source_axiom.
  repeat setoid_rewrite holds_or. rewrite zfc_fixed_source_formula_correct,
    numerical_closed_separation_formula_correct,numerical_closed_replacement_formula_correct.
  reflexivity.
Qed.
Theorem numerical_zfc_source_axiom_unary :
  bounded 1 (numerical_zfc_source_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Theorem numerical_zfc_source_axiom_definable M : Definable1 M (numerical_zfc_source_axiom M).
Proof.
  exists (numerical_zfc_source_axiom_formula $0),(fun _ => zeroM M).
  intro z. symmetry. apply numerical_zfc_source_axiom_formula_correct.
Qed.

Theorem numerical_separation_instance_total M phi n : source_bounded M phi (succM M n) ->
  exists z, numerical_separation_instance M phi n z.
Proof.
  intro Hbound. destruct (schema_renaming_total M SepBody phi) as [body Hb].
  destruct (sf_separation_constructor_total M body) as [open_code Ho].
  destruct (all_prefix_total M n open_code) as [z Hz].
  exists z. split; [exact Hbound|]. exists body,open_code. auto.
Qed.
Theorem numerical_replacement_instance_total M phi n :
  source_bounded M phi (succM M (succM M n)) ->
  exists z, numerical_replacement_instance M phi n z.
Proof.
  intro Hbound. destruct (schema_renaming_total M RepA phi) as [a Ha].
  destruct (schema_renaming_total M RepB phi) as [b Hb].
  destruct (schema_renaming_total M RepC phi) as [c Hc].
  destruct (sf_replacement_constructor_total M a b c) as [open_code Ho].
  destruct (all_prefix_total M n open_code) as [z Hz].
  exists z. split; [exact Hbound|]. exists a,b,c,open_code. auto.
Qed.
Theorem numerical_separation_instance_functional M phi n z z' :
  numerical_separation_instance M phi n z -> numerical_separation_instance M phi n z' -> z=z'.
Proof.
  intros [_ [body [open_code [Hb [Ho Hz]]]]] [_ [body' [open_code' [Hb' [Ho' Hz']]]]].
  assert (Eb : body=body') by (eapply schema_renaming_functional; eassumption). subst body'.
  assert (Eo : open_code=open_code') by (eapply sf_separation_constructor_functional; eassumption). subst open_code'.
  eapply all_prefix_functional; eassumption.
Qed.
Theorem numerical_replacement_instance_functional M phi n z z' :
  numerical_replacement_instance M phi n z -> numerical_replacement_instance M phi n z' -> z=z'.
Proof.
  intros [_ [a [b [c [o [Ha [Hb [Hc [Ho Hz]]]]]]]]]
    [_ [a' [b' [c' [o' [Ha' [Hb' [Hc' [Ho' Hz']]]]]]]]].
  assert (Ea : a=a') by (eapply schema_renaming_functional; eassumption). subst a'.
  assert (Eb : b=b') by (eapply schema_renaming_functional; eassumption). subst b'.
  assert (Ec : c=c') by (eapply schema_renaming_functional; eassumption). subst c'.
  assert (Eo : o=o') by (eapply sf_replacement_constructor_functional; eassumption). subst o'.
  eapply all_prefix_functional; eassumption.
Qed.
Theorem numerical_closed_separation_is_closed M z :
  numerical_closed_separation M z -> source_bounded M z (zeroM M).
Proof. intros [H _]. exact H. Qed.
Theorem numerical_closed_replacement_is_closed M z :
  numerical_closed_replacement M z -> source_bounded M z (zeroM M).
Proof. intros [H _]. exact H. Qed.
