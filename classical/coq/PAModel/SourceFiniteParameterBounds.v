(** Free-index bounds make the finite parameter compiler independent of
    unused entries. In particular its one-free-variable output is exactly
    the ordinary capture-avoiding singleton instantiation graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBoundedCalibration SourceFiniteParameters SourceFiniteParameterProofs
  SourceFiniteParameterInstances NumericalInstantiation.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_parameter_bounded_extensional {ff} n
    (phi:@Core.form sig_empty ZFSignature.ZF_pred_sig Core.FullSyntax.full_operators ff) :
  bounded n phi ->forall names other,
  (forall i,i<n ->names i=other i) ->
  source_parameter_expression names phi=source_parameter_expression other phi.
Proof.
  intro HB. induction HB;intros names other HE.
  - destruct P;cbn [source_parameter_expression].
    all: assert (HX:sf_index (Vector.hd v)<n) by (apply (proj1 (sb_term_bounded n (Vector.hd v)));apply H;
      rewrite (sb_vector_two v);now constructor).
    all: assert (HY:sf_index (Vector.hd (Vector.tl v))<n) by (apply (proj1 (sb_term_bounded n (Vector.hd (Vector.tl v))));apply H;
      rewrite (sb_vector_two v);apply Vector.In_cons_tl;now constructor).
    all: f_equal;apply HE;assumption.
  - cbn [source_parameter_expression]. rewrite (IHHB1 names other HE),(IHHB2 names other HE).
    reflexivity.
  - cbn [source_parameter_expression].
    rewrite (IHHB (source_parameter_up names) (source_parameter_up other));[reflexivity|].
    intros [|i] HI;cbn [source_parameter_up];[reflexivity|]. rewrite HE;[reflexivity|lia].
  - reflexivity.
Qed.

Theorem source_one_parameter_instantiation M phi rho out :
  bounded 1 phi ->
  code_relation M rho (source_parameter_expression source_three_parameter_names phi) out ->
  numerical_instantiation M (code_numeral M (sf_encode phi)) (rho 0) out.
Proof.
  intros HB HG. apply (source_finite_parameter_instantiation M phi rho out).
  rewrite <- (source_parameter_bounded_extensional 1 phi HB
    source_three_parameter_names source_singleton_parameter_names);[exact HG|].
  intros [|i] HI;[reflexivity|lia].
Qed.

Print Assumptions source_parameter_bounded_extensional.
Print Assumptions source_one_parameter_instantiation.


