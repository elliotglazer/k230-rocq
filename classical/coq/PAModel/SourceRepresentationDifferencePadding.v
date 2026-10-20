(** Exact Op2 conditions move above arbitrary internally many assignment
    slots. The closed-membership operation remains the literal pinned Op2. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceDifferenceProfile
 SourceRepresentationDifferencePoints SourceRepresentationPadding SourceThreeParameterCommutation
 SourceFiniteParameters SourceFiniteParameterProofs OldFullNDSourceBridge OldNamedSyntaxBridge
 NumericalRenamingMaps NumericalRenaming.
From OldZFC Require Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded Sets.minZF.
From Stdlib Require Import Lia.
Open Scope minZFsyn.
Unset Implicit Arguments.
Lemma source_difference_operation_bounded :bounded 3(source_difference_operation $0 $1 $2).
Proof.
 rewrite source_difference_operation_literal. apply(@isolated_bounded OC.falsity_on 3),
 OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity.
Qed.
Theorem source_representation_difference_padding M count x y r x' y' r' operation padded :
 representation_padding_lookup M count x x' ->representation_padding_lookup M count y y' ->
 representation_padding_lookup M count r r' ->
 code_relation M(difference_values M x y r)source_difference_operation_expression operation ->
 code_relation M(difference_values M x' y' r')source_difference_operation_expression padded ->
 source_representation_padding M count operation padded.
Proof.
 intros HX HY HR HO HP.
 apply(source_three_parameter_renaming_commutation M(source_difference_operation $0 $1 $2)
  (difference_values M x y r)(difference_values M x' y' r') operation padded
  (code_numeral M 6)(code_numeral M 2)(code_numeral M 2) count
  source_difference_operation_bounded HO HP).
 intros[|[|[|i]]] HI;cbn[difference_values];try assumption;lia.
Qed.
Theorem source_representation_difference_condition_padding M count first second first' second' condition padded :
 source_representation_padding M count first first' ->source_representation_padding M count second second' ->
 sf_relation M SFAnd first second condition ->sf_relation M SFAnd first' second' padded ->
 source_representation_padding M count condition padded.
Proof.
 intros HF HS HC HP. apply(proj2(numerical_renaming_binary M SFAnd first second condition
  (code_numeral M 6)(code_numeral M 2)(code_numeral M 2)count padded(or_introl eq_refl) HC)).
 exists first',second'. exact(conj HF(conj HS HP)).
Qed.
Print Assumptions source_difference_operation_bounded.
Print Assumptions source_representation_difference_padding.
Print Assumptions source_representation_difference_condition_padding.
