(** Global standard-model exactness.  The external axiom predicate below
    uses the library's actual minZFeq' list, the two already calibrated
    Foundation/Choice formulas, and CLOSED universal schema instances.
    No input-bound side condition is built into this external predicate. *)
From PAModel Require Import Model StandardModel CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded SourceBoundedCalibration SourceCodeDecoding
  NumericalSetClosure NumericalZFCAxioms NumericalZFCCalibration
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Facts Sets.minZF.
From Stdlib Require Import List Lia.
Import ListNotations.
Unset Implicit Arguments.
#[local] Instance exact_empty_dec (x y:sig_empty) : Dec.dec (x=y).
Proof. destruct x. Qed.
#[local] Instance exact_pred_dec (x y:ZF_Preds) : Dec.dec (x=y).
Proof. unfold Dec.dec;decide equality. Qed.

Definition separation_restore : nat->sf_term :=
  $0 .: $0 .: $0 .: (S >> var).
Definition replacement_restore : nat->sf_term :=
  $0 .: $1 .: $0 .: (fun i => $(S(S i))).

Lemma separation_restore_identity (phi:sf_form) :
  phi[sep_substitution][separation_restore]=phi.
Proof.
  rewrite subst_comp. apply subst_id. intros [|i];
    cbn [sep_substitution separation_restore funcomp scons subst_term];reflexivity.
Qed.
Lemma replacement_restore_identity (phi:sf_form) :
  phi[rep_substitution_A][replacement_restore]=phi.
Proof.
  rewrite subst_comp. apply subst_id. intros [|[|i]];
    cbn [rep_substitution_A replacement_restore funcomp scons subst_term];reflexivity.
Qed.

Lemma source_separation_bound_inv (phi:sf_form) n :
  bounded n (ax_sep' phi) -> bounded (S n) phi.
Proof.
  intro H. apply (proj2 (bounded_comp_eq _ _)) in H.
  unfold ax_sep' in H. cbn in H.
  assert (Hb : bounded (S(S(S n))) phi[sep_substitution]).
  { apply (proj1 (bounded_comp_eq _ _)). exact (proj2 (proj2 (proj1 H))). }
  rewrite <-separation_restore_identity.
  eapply subst_bounded_max; [|exact Hb].
  intros [|[|[|i]]] Hi; cbn [separation_restore funcomp scons];constructor;lia.
Qed.
Lemma source_replacement_bound_inv (phi:sf_form) n :
  bounded n (ax_rep' phi) -> bounded (S(S n)) phi.
Proof.
  intro H. apply (proj2 (bounded_comp_eq _ _)) in H.
  unfold ax_rep',fun_rel' in H. cbn in H.
  assert (Hb : bounded (S(S(S n))) phi[rep_substitution_A]).
  { apply (proj1 (bounded_comp_eq _ _)). exact (proj1 (proj1 H)). }
  rewrite <-replacement_restore_identity.
  eapply subst_bounded_max; [|exact Hb].
  intros [|[|[|i]]] Hi; cbn [replacement_restore funcomp scons];constructor;lia.
Qed.

Lemma standard_prefix_bound_inv n (phi:sf_form) :
  bounded 0 (forall_times n phi) -> bounded n phi.
Proof.
  intro H. apply source_bounded_sf_encode.
  apply (proj1 (all_prefix_closed_iff natModel n (sf_encode phi)
    (sf_encode (forall_times n phi)) (proj2 (all_prefix_forall_times n phi _) eq_refl))).
  now apply source_bounded_sf_encode.
Qed.

Definition standard_zfc_source_axiom (psi:sf_form) : Prop :=
  In psi minZFeq' \/ psi=source_foundation \/ psi=source_choice \/
  (exists phi n, psi=forall_times n (ax_sep' phi) /\ bounded 0 psi) \/
  (exists phi n, psi=forall_times n (ax_rep' phi) /\ bounded 0 psi).

Lemma standard_fixed_source_iff (psi:sf_form) :
  (exists tag, psi=zfc_fixed_source tag) <->
  In psi minZFeq' \/ psi=source_foundation \/ psi=source_choice.
Proof.
  split.
  - intros [tag ->]. destruct tag; cbn [zfc_fixed_source minZFeq' minZF' List.In]; tauto.
  - intros [H|[H|H]].
    + cbn [minZFeq' minZF' List.In] in H.
      repeat match type of H with _ \/ _ => destruct H as [H|H] end;
        try contradiction; subst psi;
        first [solve [exists ZFCRefl;reflexivity]|solve [exists ZFCSym;reflexivity]|solve [exists ZFCTrans;reflexivity]|solve [exists ZFCEqElem;reflexivity]|solve [exists ZFCExt;reflexivity]|solve [exists ZFCEmpty;reflexivity]|solve [exists ZFCPair;reflexivity]|solve [exists ZFCUnion;reflexivity]|solve [exists ZFCPower;reflexivity]|solve [exists ZFCOmega;reflexivity]].
    + exists ZFCFoundation;exact H.
    + exists ZFCChoice;exact H.
Qed.

Theorem numerical_zfc_source_axiom_standard_exact z :
  numerical_zfc_source_axiom natModel z <->
  exists psi:sf_form, standard_zfc_source_axiom psi /\ sf_encode psi=z.
Proof.
  split.
  - intros [[tag Htag]|[Hsep|Hrep]].
    + exists (zfc_fixed_source tag). split.
      * unfold standard_zfc_source_axiom.
        pose proof (proj1 (standard_fixed_source_iff _) (ex_intro _ tag eq_refl)) as H.
        tauto.
      * unfold zfc_source_graph in Htag. rewrite code_relation_natModel in Htag.
        rewrite zfc_fixed_source_expression_value in Htag. symmetry;exact Htag.
    + destruct Hsep as [Hclosed [f [n Hinst]]].
      destruct (proj1 (source_bounded_decode f (S n)) (proj1 Hinst)) as [phi [Hphi Ephi]].
      subst f. apply numerical_separation_instance_standard in Hinst.
      destruct Hinst as [_ ->]. exists (forall_times n (ax_sep' phi)). split; [|reflexivity].
      unfold standard_zfc_source_axiom. right;right;right;left.
      exists phi,n. split; [reflexivity|]. now apply source_bounded_sf_encode.
    + destruct Hrep as [Hclosed [f [n Hinst]]].
      destruct (proj1 (source_bounded_decode f (S(S n))) (proj1 Hinst)) as [phi [Hphi Ephi]].
      subst f. apply numerical_replacement_instance_standard in Hinst.
      destruct Hinst as [_ ->]. exists (forall_times n (ax_rep' phi)). split; [|reflexivity].
      unfold standard_zfc_source_axiom. right;right;right;right.
      exists phi,n. split; [reflexivity|]. now apply source_bounded_sf_encode.
  - intros [psi [Hpsi <-]].
    destruct Hpsi as [Hbase|[Hfound|[Hchoice|[Hsep|Hrep]]]].
    + destruct (proj2 (standard_fixed_source_iff psi) (or_introl Hbase)) as [tag ->].
      apply standard_fixed_is_source_axiom.
    + subst psi. apply (standard_fixed_is_source_axiom ZFCFoundation).
    + subst psi. apply (standard_fixed_is_source_axiom ZFCChoice).
    + destruct Hsep as [phi [n [-> Hclosed]]]. apply standard_separation_is_source_axiom.
      apply source_separation_bound_inv. now apply standard_prefix_bound_inv in Hclosed.
    + destruct Hrep as [phi [n [-> Hclosed]]]. apply standard_replacement_is_source_axiom.
      apply source_replacement_bound_inv. now apply standard_prefix_bound_inv in Hclosed.
Qed.

Corollary numerical_zfc_axiom_formula_standard_exact z :
  holds natModel (z .: fun _ => 0) (numerical_zfc_source_axiom_formula $0) <->
  exists psi:sf_form, standard_zfc_source_axiom psi /\ sf_encode psi=z.
Proof.
  rewrite numerical_zfc_source_axiom_formula_correct.
  apply numerical_zfc_source_axiom_standard_exact.
Qed.
