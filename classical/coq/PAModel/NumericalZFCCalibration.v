(** Exact calibration of the source axiom recognizers on standard finite
    formulas.  This is not a source proof-calculus interpretation. *)
From PAModel Require Import Model Arithmetic CodeExpressions StandardModel
  SetFormulaCodes SetSchemaConstructors NumericalSetClosure SourceBounded
  SourceBoundedCalibration SchemaRenamingDescriptors SchemaRenamingCalibration
  NumericalZFCAxioms ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Instance schema_empty_dec (x y:sig_empty) : Dec.dec (x=y).
Proof. destruct x. Qed.
#[local] Instance schema_pred_dec (x y:ZF_Preds) : Dec.dec (x=y).
Proof. unfold Dec.dec;decide equality. Qed.

Theorem numerical_separation_instance_standard (phi:sf_form) n z :
  numerical_separation_instance natModel (sf_encode phi) n z <->
  bounded (S n) phi /\ z=sf_encode (forall_times n (ax_sep' phi)).
Proof.
  unfold numerical_separation_instance.
  rewrite source_bounded_sf_encode. split.
  - intros [Hb [body [open_code [Hr [Hc Hp]]]]].
    apply schema_renaming_standard_iff in Hr. subst body.
    change (sf_separation_constructor natModel
      (sf_encode (source_sep_body phi)) open_code) in Hc.
    apply sf_separation_constructor_standard in Hc. subst open_code.
    apply all_prefix_forall_times in Hp. auto.
  - intros [Hb ->]. split; [exact Hb|].
    exists (sf_encode (source_sep_body phi)), (sf_encode (ax_sep' phi)).
    split; [apply schema_renaming_source_calibration|].
    split; [apply sf_separation_constructor_standard;reflexivity|].
    apply all_prefix_forall_times;reflexivity.
Qed.

Theorem numerical_replacement_instance_standard (phi:sf_form) n z :
  numerical_replacement_instance natModel (sf_encode phi) n z <->
  bounded (S(S n)) phi /\ z=sf_encode (forall_times n (ax_rep' phi)).
Proof.
  unfold numerical_replacement_instance.
  rewrite source_bounded_sf_encode. split.
  - intros [Hb [a [b [c [open_code [Ha [Hb' [Hc [Hopen Hp]]]]]]]]].
    apply schema_renaming_standard_iff in Ha,Hb',Hc. subst a b c.
    change (sf_replacement_constructor natModel
      (sf_encode (source_rep_body_A phi)) (sf_encode (source_rep_body_B phi))
      (sf_encode (source_rep_body_C phi)) open_code) in Hopen.
    apply sf_replacement_constructor_standard in Hopen. subst open_code.
    apply all_prefix_forall_times in Hp. auto.
  - intros [Hb ->]. split; [exact Hb|].
    exists (sf_encode (source_rep_body_A phi)), (sf_encode (source_rep_body_B phi)),
      (sf_encode (source_rep_body_C phi)), (sf_encode (ax_rep' phi)).
    split; [apply schema_renaming_source_calibration|].
    split; [apply schema_renaming_source_calibration|].
    split; [apply schema_renaming_source_calibration|].
    split; [apply sf_replacement_constructor_standard;reflexivity|].
    apply all_prefix_forall_times;reflexivity.
Qed.

Lemma schema_substitution_bounded s (phi:sf_form) k l :
  bounded k phi ->
  (forall i, i<k -> sf_index (schema_substitution s i)<l) ->
  bounded l phi[schema_substitution s].
Proof.
  intros Hphi Hmap. eapply subst_bounded_max; [|exact Hphi].
  intros i Hi. specialize (Hmap i Hi).
  destruct (schema_substitution s i) as [j|[]]. constructor;exact Hmap.
Qed.

Lemma source_separation_bounded (phi:sf_form) n :
  bounded (S n) phi -> bounded n (ax_sep' phi).
Proof.
  intro Hphi.
  assert (Hb : bounded (S(S(S n))) phi[sep_substitution]).
  { apply (schema_substitution_bounded SepBody phi (S n)); [exact Hphi|].
    intros [|i] Hi; cbn [schema_substitution].
    all: rewrite sep_substitution_index;lia. }
  apply (proj1 (bounded_comp_eq _ _)). apply (proj2 (bounded_comp_eq _ _)) in Hb.
  unfold ax_sep'. cbn. cbn [sep_substitution] in Hb. intuition lia.
Qed.

Lemma source_replacement_bounded (phi:sf_form) n :
  bounded (S(S n)) phi -> bounded n (ax_rep' phi).
Proof.
  intro Hphi.
  assert (HA : bounded (S(S(S n))) phi[rep_substitution_A]).
  { apply (schema_substitution_bounded RepA phi (S(S n))); [exact Hphi|].
    intros [|[|i]] Hi; cbn [schema_substitution]; rewrite rep_substitution_A_index;lia. }
  assert (HB : bounded (S(S(S n))) phi[rep_substitution_B]).
  { apply (schema_substitution_bounded RepB phi (S(S n))); [exact Hphi|].
    intros [|[|i]] Hi; cbn [schema_substitution]; rewrite rep_substitution_B_index;lia. }
  assert (HC : bounded (S(S(S(S n)))) phi[rep_substitution_C]).
  { apply (schema_substitution_bounded RepC phi (S(S n))); [exact Hphi|].
    intros [|[|i]] Hi; cbn [schema_substitution]; rewrite rep_substitution_C_index;lia. }
  apply (proj1 (bounded_comp_eq _ _)). apply (proj2 (bounded_comp_eq _ _)) in HA,HB,HC.
  unfold ax_rep',fun_rel'. cbn.
  cbn [rep_substitution_A] in HA. cbn [rep_substitution_B] in HB.
  cbn [rep_substitution_C] in HC. intuition lia.
Qed.

Theorem standard_separation_is_source_axiom (phi:sf_form) n :
  bounded (S n) phi ->
  numerical_zfc_source_axiom natModel (sf_encode (forall_times n (ax_sep' phi))).
Proof.
  intro Hb. right;left. split.
  - apply (all_prefix_closes natModel n (sf_encode (ax_sep' phi))).
    + apply source_bounded_sf_encode. now apply source_separation_bounded.
    + apply all_prefix_forall_times;reflexivity.
  - exists (sf_encode phi),n. apply numerical_separation_instance_standard. auto.
Qed.

Theorem standard_replacement_is_source_axiom (phi:sf_form) n :
  bounded (S(S n)) phi ->
  numerical_zfc_source_axiom natModel (sf_encode (forall_times n (ax_rep' phi))).
Proof.
  intro Hb. right;right. split.
  - apply (all_prefix_closes natModel n (sf_encode (ax_rep' phi))).
    + apply source_bounded_sf_encode. now apply source_replacement_bounded.
    + apply all_prefix_forall_times;reflexivity.
  - exists (sf_encode phi),n. apply numerical_replacement_instance_standard. auto.
Qed.

Theorem standard_fixed_is_source_axiom tag :
  numerical_zfc_source_axiom natModel (sf_encode (zfc_fixed_source tag)).
Proof.
  left. exists tag. unfold zfc_source_graph. rewrite code_relation_natModel.
  symmetry. apply zfc_fixed_source_expression_value.
Qed.
