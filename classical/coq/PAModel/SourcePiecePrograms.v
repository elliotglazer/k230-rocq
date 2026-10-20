(** Fixed logical programs combining actual piece-monotonicity proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalContexts NumericalSourceFull
  SourcePropositionalTemplates SourceDescriptorClosure SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_piece_curried_template left right:=SPTImpl(SPTSlot 0)(SPTImpl(SPTSlot 1)
  (SPTImpl(SPTSlot 2)(SPTImpl left right))).

Lemma source_piece_program_use A left right:
  source_prop_program A(source_piece_curried_template left right) ->source_prop_program A(SPTSlot 0) ->
  source_prop_program A(SPTSlot 1) ->source_prop_program A(SPTSlot 2) ->source_prop_program A left ->
  source_prop_program A right.
Proof.
  intros HP H0 H1 H2 HL.
  exact(SPTIE A left right(SPTIE A(SPTSlot 2)(SPTImpl left right)
    (SPTIE A(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl left right))
      (SPTIE A(SPTSlot 0)(SPTImpl(SPTSlot 1)(SPTImpl(SPTSlot 2)(SPTImpl left right)))HP H0)H1)H2)HL).
Qed.

Theorem source_piece_conjunction_mono_program:source_prop_program
  [source_piece_curried_template(SPTSlot 3)(SPTSlot 4);source_piece_curried_template(SPTSlot 5)(SPTSlot 6)]
  (source_piece_curried_template(SPTAnd(SPTSlot 3)(SPTSlot 5))(SPTAnd(SPTSlot 4)(SPTSlot 6))).
Proof.
  unfold source_piece_curried_template at 3. apply SPTII,SPTII,SPTII,SPTII,SPTCI.
  - apply(source_piece_program_use _(SPTSlot 3)(SPTSlot 4)).
    + apply SPTCtx. right;right;right;right;now left.
    + apply SPTCtx. right;right;right;now left.
    + apply SPTCtx. right;right;now left.
    + apply SPTCtx. right;now left.
    + eapply SPTCE1,SPTCtx. now left.
  - apply(source_piece_program_use _(SPTSlot 5)(SPTSlot 6)).
    + apply SPTCtx. right;right;right;right;right;now left.
    + apply SPTCtx. right;right;right;now left.
    + apply SPTCtx. right;right;now left.
    + apply SPTCtx. right;now left.
    + eapply SPTCE2,SPTCtx. now left.
Qed.

Theorem source_piece_mono_identity_program:source_prop_program[]
  (source_piece_curried_template(SPTSlot 3)(SPTSlot 3)).
Proof. unfold source_piece_curried_template. apply SPTII,SPTII,SPTII,SPTII,SPTCtx. now left. Qed.

Theorem source_piece_prop_zero M a(program:source_prop_program[]a)rho k out:
  (forall i,source_bounded M(rho i)k) ->code_relation M rho(source_prop_expression a)out ->source_zfr_provable M out.
Proof.
  intros HB HG. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_provable_from_empty M ZFRSourceDescriptor out).
  apply(source_prop_program_sound M[]a program rho k(zeroM M)(zeroM M)(zeroM M)out HB).
  - apply context_bounded_empty.
  - intros f[]out' H.
  - exact HG.
Qed.

Print Assumptions source_piece_conjunction_mono_program.
Print Assumptions source_piece_mono_identity_program.
Print Assumptions source_piece_prop_zero.
