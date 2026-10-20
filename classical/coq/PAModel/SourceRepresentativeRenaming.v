(** Replace only the free representative name0. The exact square with
    Dn rotation moves an auxiliary representative from r to succ(r). *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalRenamingMaps NumericalRenaming SourceNumeralLift SourceDnStep
 SourceBounded SourceRenamingDiamond.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition representative_lookup M r i j :=renaming_lookup M r r(code_numeral M 1)(zeroM M) i j.
Lemma representative_lookup_zero M r :representative_lookup M r(zeroM M) r.
Proof. left. split;[apply coding_zero_lt_succ|apply beta_singleton]. Qed.
Lemma representative_lookup_nonzero M r i :i<>zeroM M ->representative_lookup M r i i.
Proof.
 intro HI. right. split;[|symmetry;apply coding_add_zero_r].
 intro HB. apply coding_lt_succ_cases in HB. destruct HB as[HB|E];[exact(coding_not_lt_zero M i HB)|contradiction].
Qed.
Lemma representative_lift_one M r b c n :renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 renaming_lookup M b c n(zeroM M)(code_numeral M 1)(succM M r).
Proof.
 intro HL. exact(proj2(renaming_lift_tail M r r(code_numeral M 1)(zeroM M) b c n(zeroM M) r HL)
   (representative_lookup_zero M r)).
Qed.
Lemma representative_lift_fixed M r b c n i :renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 i<>code_numeral M 1 ->renaming_lookup M b c n(zeroM M) i i.
Proof.
 intros HL HI. destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)
   (fun ax H rho=>axioms M ax rho H) i)as[E|[j E]];subst i.
 - exact(proj2(renaming_lift_head M r r(code_numeral M 1)(zeroM M) b c n(zeroM M) HL) eq_refl).
 - apply(proj2(renaming_lift_tail M r r(code_numeral M 1)(zeroM M) b c n j j HL)).
   apply representative_lookup_nonzero. intro E. subst j. contradiction.
Qed.

Definition source_representative_renaming M r f g :=numerical_renaming M f r r(code_numeral M 1)(zeroM M) g.
Definition source_representative_renaming_formula(r f g:term):form :=numerical_renaming_formula f r r(num 1) zero g.
Theorem source_representative_renaming_formula_correct M rho r f g :
 holds M rho(source_representative_renaming_formula r f g) <->
 source_representative_renaming M(evalM M rho r)(evalM M rho f)(evalM M rho g).
Proof. unfold source_representative_renaming_formula,source_representative_renaming.
 rewrite numerical_renaming_formula_correct. now repeat setoid_rewrite code_eval_num. Qed.
Theorem source_representative_renaming_total M r f :exists g,source_representative_renaming M r f g.
Proof. apply numerical_renaming_total. Qed.
Theorem source_representative_renaming_functional M r f g h :
 source_representative_renaming M r f g ->source_representative_renaming M r f h ->g=h.
Proof. apply numerical_renaming_functional. Qed.

Theorem source_representative_dn_rotation_square M f r renamed rotated out b c n k :
 source_bounded M f k ->~coding_lt M r(code_numeral M 2) ->
 source_representative_renaming M(succM M r) f renamed ->
 numerical_renaming M f(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) rotated ->
 renaming_lift M r r(code_numeral M 1)(zeroM M) b c n ->
 numerical_renaming M rotated b c n(zeroM M) out ->
 numerical_renaming M renamed(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) out.
Proof.
 intros HF HR HName HRot HL HOut.
 apply(numerical_source_renaming_diamond M f k
   (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)
   (succM M r)(succM M r)(code_numeral M 1)(zeroM M)
   b c n(zeroM M)
   (code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M)
   rotated renamed out HF HRot HName HOut).
 intros i j l m _ HJ HM HNameI.
 destruct(environment_lt_cases M i(code_numeral M 3))as[HSmall|HLarge].
 - destruct(source_numeral_initial_segment M 3 i HSmall)as(index&HIndex&->).
   destruct index as[|[|[|index]]];try lia.
   + assert(EJ:j=code_numeral M 1)by(eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_zero]). subst j.
     assert(EL:l=succM M r)by(eapply renaming_lookup_functional;[exact HNameI|apply representative_lookup_zero]). subst l.
     assert(EM:m=succM M r)by(eapply renaming_lookup_functional;[exact HM|apply representative_lift_one;exact HL]). subst m.
     apply source_dn_rotate_outside. intro HBad. apply HR. exact(proj1(coding_lt_succ_cancel M r(code_numeral M 2)) HBad).
   + assert(EJ:j=code_numeral M 2)by(eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_one]). subst j.
     assert(EL:l=code_numeral M 1).
     { eapply renaming_lookup_functional;[exact HNameI|apply representative_lookup_nonzero]. intro E. exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)). }
     subst l. assert(EM:m=code_numeral M 2).
     { eapply renaming_lookup_functional;[exact HM|apply(representative_lift_fixed M r b c n);[exact HL|]].
       intro E. apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)). }
     subst m. apply source_dn_rotate_one.
   + assert(EJ:j=zeroM M)by(eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_two]). subst j.
     assert(EL:l=code_numeral M 2).
     { eapply renaming_lookup_functional;[exact HNameI|apply representative_lookup_nonzero]. intro E. exact(Model.zero_ne_succ M(code_numeral M 1)(eq_sym E)). }
     subst l. assert(EM:m=zeroM M).
     { eapply renaming_lookup_functional;[exact HM|apply(representative_lift_fixed M r b c n);[exact HL|]].
       exact(Model.zero_ne_succ M(zeroM M)). }
     subst m. apply source_dn_rotate_two.
 - assert(EJ:j=i)by(eapply renaming_lookup_functional;[exact HJ|apply source_dn_rotate_outside;exact HLarge]). subst j.
   assert(HZero:i<>zeroM M).
   { intro E. subst i. exact(HLarge(coding_zero_lt_succ M(code_numeral M 2))). }
   assert(HOne:i<>code_numeral M 1).
   { intro E. subst i. apply HLarge. apply coding_lt_succ_cancel,coding_zero_lt_succ. }
   assert(EL:l=i)by(eapply renaming_lookup_functional;[exact HNameI|apply representative_lookup_nonzero;exact HZero]). subst l.
   assert(EM:m=i)by(eapply renaming_lookup_functional;[exact HM|apply(representative_lift_fixed M r b c n);assumption]). subst m.
   apply source_dn_rotate_outside. exact HLarge.
Qed.
Print Assumptions source_representative_renaming_formula_correct.
Print Assumptions source_representative_dn_rotation_square.


