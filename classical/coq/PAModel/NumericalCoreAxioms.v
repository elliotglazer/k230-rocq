(** Source axioms for ZFc: minZFeq' with closed Separation and Replacement
    instances, excluding Foundation and Choice. This is the current-library
    reconstruction of Std_iface.ZFc used by KQuotZFTransfer. Its arithmetic
    predicate and current-library syntax correspondence are proved here.

    Literal comparison to the separately namespaced legacy Std_iface still
    requires a source correspondence audit, including closedf = fb 0 versus
    this library's bounded 0. This file imports no legacy source definitions
    and proves no K-provability or consistency comparison. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs SentenceBounds StandardModel
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundedCalibration
  SourceCodeDecoding NumericalSetClosure NumericalZFCAxioms NumericalZFCCalibration
  NumericalZFCExactness FixedSourceBounds ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition zfc_core_fixed_tags : list zfc_fixed_axiom :=
  [ZFCRefl; ZFCSym; ZFCTrans; ZFCEqElem; ZFCExt;
   ZFCEmpty; ZFCPair; ZFCUnion; ZFCPower; ZFCOmega].

Definition numerical_zfc_core_source_axiom M z :=
  (exists tag, In tag zfc_core_fixed_tags /\ zfc_source_graph M tag z) \/
  numerical_closed_separation M z \/ numerical_closed_replacement M z.

Definition numerical_zfc_core_source_axiom_formula (z : pa_term) : pa_form :=
  zfc_source_disjunction zfc_core_fixed_tags z ∨
  (numerical_closed_separation_formula z ∨ numerical_closed_replacement_formula z).

Local Opaque holds zfc_source_disjunction
  numerical_closed_separation_formula numerical_closed_replacement_formula.
Theorem numerical_zfc_core_source_axiom_formula_correct M rho z :
  holds M rho (numerical_zfc_core_source_axiom_formula z) <->
  numerical_zfc_core_source_axiom M (evalM M rho z).
Proof.
  unfold numerical_zfc_core_source_axiom_formula,numerical_zfc_core_source_axiom.
  repeat setoid_rewrite holds_or.
  rewrite zfc_source_disjunction_correct,numerical_closed_separation_formula_correct,
    numerical_closed_replacement_formula_correct. reflexivity.
Qed.

Theorem numerical_zfc_core_source_axiom_unary :
  bounded 1 (numerical_zfc_core_source_axiom_formula $0).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem numerical_zfc_core_source_axiom_definable M :
  Definable1 M (numerical_zfc_core_source_axiom M).
Proof.
  exists (numerical_zfc_core_source_axiom_formula $0),(fun _=>zeroM M).
  intro z. symmetry. apply numerical_zfc_core_source_axiom_formula_correct.
Qed.

Theorem numerical_zfc_core_source_axiom_closed M z :
  numerical_zfc_core_source_axiom M z -> source_bounded M z (zeroM M).
Proof.
  intros [[tag [_ Htag]]|[Hsep|Hrep]].
  - exact (zfc_source_graph_closed M tag z Htag).
  - exact (numerical_closed_separation_is_closed M z Hsep).
  - exact (numerical_closed_replacement_is_closed M z Hrep).
Qed.

Theorem numerical_zfc_core_source_axiom_in_zfc M z :
  numerical_zfc_core_source_axiom M z -> numerical_zfc_source_axiom M z.
Proof.
  intros [[tag [_ Htag]]|[Hsep|Hrep]].
  - left. now exists tag.
  - right;now left.
  - right;now right.
Qed.

Definition standard_zfc_core_source_axiom (psi:sf_form) : Prop :=
  In psi minZFeq' \/
  (exists phi n,psi=forall_times n (ax_sep' phi) /\ bounded 0 psi) \/
  (exists phi n,psi=forall_times n (ax_rep' phi) /\ bounded 0 psi).

Lemma standard_zfc_core_fixed_iff (psi:sf_form) :
  (exists tag,In tag zfc_core_fixed_tags /\ psi=zfc_fixed_source tag) <->
  In psi minZFeq'.
Proof.
  split.
  - intros [tag [HT ->]]. destruct tag;
      cbn [zfc_core_fixed_tags List.In zfc_fixed_source minZFeq' minZF'] in *;
      intuition congruence.
  - intro H. cbn [minZFeq' minZF' List.In] in H.
    repeat match type of H with _ \/ _ => destruct H as [H|H] end;
      try contradiction; subst psi;
      first
      [ solve [exists ZFCRefl;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCSym;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCTrans;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCEqElem;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCExt;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCEmpty;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCPair;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCUnion;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCPower;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]]
      | solve [exists ZFCOmega;split;[cbn [zfc_core_fixed_tags List.In];tauto|reflexivity]] ].
Qed.

Theorem standard_zfc_core_source_axiom_closed psi :
  standard_zfc_core_source_axiom psi -> bounded 0 psi.
Proof.
  intros [Hbase|[Hsep|Hrep]].
  - destruct (proj2 (standard_zfc_core_fixed_iff psi) Hbase) as [tag [_ ->]].
    apply zfc_fixed_source_closed.
  - destruct Hsep as [phi [n [_ H]]]. exact H.
  - destruct Hrep as [phi [n [_ H]]]. exact H.
Qed.

Theorem numerical_zfc_core_source_axiom_standard_exact z :
  numerical_zfc_core_source_axiom natModel z <->
  exists psi:sf_form,standard_zfc_core_source_axiom psi /\ sf_encode psi=z.
Proof.
  split.
  - intros [[tag [HT Htag]]|[Hsep|Hrep]].
    + exists (zfc_fixed_source tag). split.
      * left. apply standard_zfc_core_fixed_iff. exists tag. auto.
      * unfold zfc_source_graph in Htag. rewrite code_relation_natModel in Htag.
        rewrite zfc_fixed_source_expression_value in Htag. symmetry;exact Htag.
    + destruct Hsep as [Hclosed [f [n Hinst]]].
      destruct (proj1 (source_bounded_decode f (S n)) (proj1 Hinst)) as [phi [Hphi Ephi]].
      subst f. apply numerical_separation_instance_standard in Hinst.
      destruct Hinst as [_ ->]. exists (forall_times n (ax_sep' phi)). split;[|reflexivity].
      right;left. exists phi,n. split;[reflexivity|]. now apply source_bounded_sf_encode.
    + destruct Hrep as [Hclosed [f [n Hinst]]].
      destruct (proj1 (source_bounded_decode f (S(S n))) (proj1 Hinst)) as [phi [Hphi Ephi]].
      subst f. apply numerical_replacement_instance_standard in Hinst.
      destruct Hinst as [_ ->]. exists (forall_times n (ax_rep' phi)). split;[|reflexivity].
      right;right. exists phi,n. split;[reflexivity|]. now apply source_bounded_sf_encode.
  - intros [psi [Hpsi <-]]. destruct Hpsi as [Hbase|[Hsep|Hrep]].
    + destruct (proj2 (standard_zfc_core_fixed_iff psi) Hbase) as [tag [HT ->]].
      left. exists tag. split;[exact HT|]. unfold zfc_source_graph.
      rewrite code_relation_natModel,zfc_fixed_source_expression_value. reflexivity.
    + destruct Hsep as [phi [n [-> Hclosed]]]. right;left. split.
      * now apply source_bounded_sf_encode.
      * exists (sf_encode phi),n. apply numerical_separation_instance_standard.
        split;[|reflexivity]. apply source_separation_bound_inv.
        exact (standard_prefix_bound_inv n (ax_sep' phi) Hclosed).
    + destruct Hrep as [phi [n [-> Hclosed]]]. right;right. split.
      * now apply source_bounded_sf_encode.
      * exists (sf_encode phi),n. apply numerical_replacement_instance_standard.
        split;[|reflexivity]. apply source_replacement_bound_inv.
        exact (standard_prefix_bound_inv n (ax_rep' phi) Hclosed).
Qed.

Print Assumptions numerical_zfc_core_source_axiom_formula_correct.
Print Assumptions numerical_zfc_core_source_axiom_closed.
Print Assumptions standard_zfc_core_fixed_iff.
Print Assumptions numerical_zfc_core_source_axiom_standard_exact.
