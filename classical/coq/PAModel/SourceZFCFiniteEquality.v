(** Numeral calibration of fixed finite equality proofs. This does not
    interpret an arbitrary internal K proof or specialize internal names. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes ZFCFiniteAxiomTemplates
  ZFCFiniteSourceCodes NumericalZFCAxioms SourceNumeralLift SourceZFCProvability
  FiniteSourceEquality.
From Undecidability.FOL Require Import Deduction.FullND Sets.minZF.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Theorem source_zfc_fixed_finite_proof M (A:list sf_form) (phi:sf_form) :
  (forall psi,In psi A -> exists tag,psi=zfc_fixed_source tag) ->
  A ⊢C phi -> source_zfc_provable M (code_numeral M (sf_encode phi)).
Proof.
  intros HAx HP. destruct (source_model_context_total M A) as (b&c&n&HC).
  exists b,c,n. split.
  - intros f HF. apply (proj1 (source_model_context_member_iff M b c n A f HC)) in HF.
    destruct HF as (psi&HI&->). destruct (HAx psi HI) as [tag ->].
    left. exists tag. exact (source_formula_numeral_graph M (zfc_fixed_source tag)).
  - exact (source_full_forward_model M A phi HP b c n HC).
Qed.

Theorem source_zfc_finite_equality_matrix M row :
  source_zfc_provable M (code_numeral M (sf_encode (finite_equality_matrix row))).
Proof.
  apply (source_zfc_fixed_finite_proof M finite_equality_axioms (finite_equality_matrix row));
    [|exact (finite_equality_matrix_derivation row)].
  intros psi HI. unfold finite_equality_axioms in HI.
  destruct HI as [<-|[<-|[<-|[<-|[]]]]].
  - exists ZFCRefl. reflexivity.
  - exists ZFCSym. reflexivity.
  - exists ZFCTrans. reflexivity.
  - exists ZFCEqElem. reflexivity.
Qed.

Print Assumptions source_zfc_fixed_finite_proof.
Print Assumptions source_zfc_finite_equality_matrix.
