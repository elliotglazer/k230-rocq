(** Native carrier formulas remain literally fixed under the support
 projection. This is proved from the actual renaming diamond, including
 the fresh transposition, rather than an assumed free-variable analysis. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceZeroTransposition SourceCarrierRenaming SourceNativeSupportProjection SourceRenamingDiamond SourceRenamingBounds SourceRenamingWellformedness
 SourceShiftSpecialization NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_transposed_bounded_projection_fixed M original live fresh tb tc out count rb rc:
 source_bounded M original live->coding_lt M live fresh->source_zero_transposition M fresh tb tc->
 numerical_renaming M original tb tc(succM M fresh)(zeroM M)out->
 source_native_support_projection M live fresh count rb rc->numerical_renaming M out rb rc count(zeroM M)out.
Proof.
 intros BO LF HT ROut HP.
 destruct(source_renaming_range_bound M tb tc(succM M fresh)(zeroM M)live)as(km&HRange).
 pose proof(numerical_renaming_preserves_bound M original tb tc(succM M fresh)(zeroM M)out live km BO ROut HRange)as BOut.
 apply(numerical_source_renaming_diamond M original live tb tc(succM M fresh)(zeroM M)
  tb tc(succM M fresh)(zeroM M)(zeroM M)(zeroM M)(zeroM M)(zeroM M)
  rb rc count(zeroM M)out out out BO ROut ROut(source_valid_identity M out km BOut)).
 intros i j l m HI HJ HM HL.
 pose proof(renaming_lookup_functional M tb tc(succM M fresh)(zeroM M)i j l HJ HL)as E;subst l.
 pose proof(renaming_lookup_functional M(zeroM M)(zeroM M)(zeroM M)(zeroM M)j m j HM(source_empty_renaming_lookup M j))as E;subst m.
 apply(proj1(HT i j))in HJ. destruct HJ as[[-> ->]|[[E ->]|[_[_ ->]]]].
 - exact(proj1(proj2 HP)).
 - subst i. exfalso. exact(@Peano.lt_neq(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)
    fresh fresh(coding_lt_trans M fresh live fresh HI LF)eq_refl).
 - exact(proj1 HP i HI).
Qed.
Theorem source_bounded_projection_fixed M f live fresh count rb rc:
 source_bounded M f live->source_native_support_projection M live fresh count rb rc->
 numerical_renaming M f rb rc count(zeroM M)f.
Proof. intros BF HP. exact(numerical_renaming_identity_on_bound M f rb rc count(zeroM M)live BF(proj1 HP)). Qed.
Print Assumptions source_transposed_bounded_projection_fixed.
Print Assumptions source_bounded_projection_fixed.
