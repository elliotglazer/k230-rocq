(** A finite arithmetic frame bound, independent of standardness of the
    names, parameter count, source formulas or produced source proofs. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceFiniteFamilyBounds SourceCommonLevelSuccessorZFR SourceCofinalGeometry SourceCofinalCommonRecipe SourceCofinalCommonWitness
 SourceMembershipBlocks SourceMembershipBlockProofs.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_cofinal_frame_bounds M start count Ks Lb seed member ordinals cover block target:
 sf_relation M SFMember seed Ks member ->source_cofinal_ordinals M Ks ordinals ->source_cofinal_cover M Ks Lb cover ->
 source_membership_block M start Lb count block ->source_cofinal_common_recipe M start count Ks target ->
 exists k,(forall f,In f[member;ordinals;cover;block] ->source_bounded M f k) /\source_bounded M target k.
Proof.
 intros HM HO HC HB HT.
 destruct(source_finite_names_bound M[addM M count start;Ks;Lb;seed])as(k&HN).
 assert(HKs:coding_lt M Ks k)by(apply HN;cbn;tauto).
 assert(HLb:coding_lt M Lb k)by(apply HN;cbn;tauto).
 assert(HSeed:coding_lt M seed k)by(apply HN;cbn;tauto).
 assert(HLast:coding_lt M(addM M count start)k)by(apply HN;cbn;tauto).
 assert(HNames:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
 { intros i HI. exact(source_bound_lt_le M(addM M i start)(succM M(addM M count start))k
   (source_common_parameter_bound M i count start(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count)))
   (proj2(coding_lt_succ_cancel M(addM M count start)k)HLast)). }
 exists k. split.
 - intros f[<-|[<-|[<-|[<-|[]]]]].
   + exact(proj2(source_bounded_accept_atom M SFMember seed Ks member k(or_introl eq_refl)HM)(conj HSeed HKs)).
   + exact(source_cofinal_ordinals_bounded M Ks ordinals k HKs HO).
   + exact(source_cofinal_cover_bounded M Ks Lb cover k HKs HLb HC).
   + exact(source_membership_block_bound M start Lb count block k HNames HLb HB).
 - exact(source_cofinal_common_recipe_bounded M start count Ks target k HNames HKs HT).
Qed.
Print Assumptions source_cofinal_frame_bounds.
