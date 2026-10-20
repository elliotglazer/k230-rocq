(** Exact shifted-parameter matrix action after one existential witness. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalRenamingMaps NumericalRenaming NumericalContextRenaming SourceBounded
 SourceRepresentationPadding SourceFiniteCutoffShift SourceSeparationSpecializationMaps.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_piece_offset_shift M count start phi shifted next ab ac an rb rc rn:
 source_bounded M phi(succM M count) ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)start ab ac an ->
 numerical_renaming M phi ab ac an start shifted ->source_cutoff_shift M 1 shifted next ->
 renaming_lift M(zeroM M)(zeroM M)(zeroM M)(succM M start)rb rc rn ->
 numerical_renaming M phi rb rc rn(succM M start)next.
Proof.
 intros HB HA HR HC HT.
 destruct(source_cutoff_one_renaming M shifted next HC)as(ub&uc&un&HU&HS).
 apply(representation_renaming_composition M phi(succM M count)ab ac an start ub uc un(code_numeral M 1)
  rb rc rn(succM M start)shifted next HB HR HS).
 intros i j v HI HJ HV.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - apply(proj1(renaming_lift_head M _ _ _ _ _ _ _ _ HA))in HJ. subst j.
   apply(proj1(renaming_lift_head M _ _ _ _ _ _ _ _ HU))in HV. subst v.
   exact(proj2(renaming_lift_head M _ _ _ _ _ _ _ _ HT)eq_refl).
 - destruct(renaming_lift_tail_inv M _ _ _ _ _ _ _ _ _ HA HJ)as(value&HValue&E). subst j.
   apply(proj1(renaming_lookup_outside M _ _ _ _ _ _(coding_not_lt_zero M idx)))in HValue. subst value.
   destruct(renaming_lift_tail_inv M _ _ _ _ _ _ _ _ _ HU HV)as(out&HOut&E). subst v.
   apply context_shift_lookup in HOut. subst out.
   apply(proj2(renaming_lift_tail M _ _ _ _ _ _ _ _ _ HT)). right. split;[apply coding_not_lt_zero|].
   rewrite(Arithmetic.add_comm M idx(succM M start)),Arithmetic.add_succ,(Arithmetic.add_comm M start idx). reflexivity.
Qed.
Print Assumptions source_piece_offset_shift.
