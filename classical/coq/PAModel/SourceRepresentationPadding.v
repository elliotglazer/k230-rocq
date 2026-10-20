(** Insert internally many assignment slots after the representative and
    carrier. Auxiliary set names above those slots remain free after Dn. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions NumericalProofs
 SetFormulaCodes SourceBounded SourceBoundMonotone SourceNumeralLift SchemaRenamingDescriptors
 NumericalEnvironments NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps NumericalSubstitution
 RenamingSubstitution SourceSubstitutionComposition SourceRenamingIdentity SourceRenamingBounds
 SourceDnStep NumericalContextRenaming SourceQuantifierRules.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Lemma representation_renaming_composition M f k ab ac an ad rb rc rn rd cb cc cn cd g h :
 source_bounded M f k ->numerical_renaming M f ab ac an ad g ->
 numerical_renaming M g rb rc rn rd h ->
 (forall i j v,coding_lt M i k ->renaming_lookup M ab ac an ad i j ->
   renaming_lookup M rb rc rn rd j v ->renaming_lookup M cb cc cn cd i v) ->
 numerical_renaming M f cb cc cn cd h.
Proof.
 intros HF HG HH HA. apply(proj2(numerical_renaming_substitution M f cb cc cn cd h)).
 apply(numerical_substitution_composition M f k ab ac an(addM M an ad) rb rc rn(addM M rn rd)
  cb cc cn(addM M cn cd) g h HF
  (proj1(numerical_renaming_substitution M f ab ac an ad g) HG)
  (proj1(numerical_renaming_substitution M g rb rc rn rd h) HH)).
 intros i j v HI HJ HV. apply(proj1(renaming_substitution_lookup M cb cc cn cd i v)).
 exact(HA i j v HI(proj2(renaming_substitution_lookup M ab ac an ad i j) HJ)
  (proj2(renaming_substitution_lookup M rb rc rn rd j v) HV)).
Qed.

Definition representation_padding_lookup M count i j :=
 renaming_lookup M(code_numeral M 6)(code_numeral M 2)(code_numeral M 2) count i j.
Lemma representation_padding_zero_lookup M count :representation_padding_lookup M count(zeroM M)(zeroM M).
Proof.
 apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_zero_lt_succ M(code_numeral M 1)))).
 apply(descriptor_beta_certificate M 6 2 0 0 2);reflexivity||lia.
Qed.
Lemma representation_padding_one_lookup M count :representation_padding_lookup M count(code_numeral M 1)(code_numeral M 1).
Proof.
 apply(proj2(renaming_lookup_inside M _ _ _ _ _ _(coding_lt_succ M(code_numeral M 1)))).
 apply(descriptor_beta_certificate M 6 2 1 1 1);reflexivity||lia.
Qed.
Lemma representation_padding_inside_lookup M count i :coding_lt M i(code_numeral M 2) ->
 representation_padding_lookup M count i i.
Proof.
 intro HI. destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
 destruct index as[|[|index]];try lia;[apply representation_padding_zero_lookup|apply representation_padding_one_lookup].
Qed.
Lemma representation_padding_outside_lookup M count i :~coding_lt M i(code_numeral M 2) ->
 representation_padding_lookup M count i(addM M i count).
Proof. intro HI. now right. Qed.
Lemma representation_padding_lookup_composition M count other i j v :
 representation_padding_lookup M count i j ->representation_padding_lookup M other j v ->
 representation_padding_lookup M(addM M count other) i v.
Proof.
 intros HJ HV. destruct(environment_lt_cases M i(code_numeral M 2))as[HI|HI].
 - assert(EJ:j=i)by(eapply renaming_lookup_functional;[exact HJ|apply representation_padding_inside_lookup;exact HI]).
   subst j. assert(EV:v=i)by(eapply renaming_lookup_functional;[exact HV|apply representation_padding_inside_lookup;exact HI]).
   subst v. apply representation_padding_inside_lookup. exact HI.
 - assert(EJ:j=addM M i count)by(eapply renaming_lookup_functional;[exact HJ|apply representation_padding_outside_lookup;exact HI]).
   subst j. assert(HJBound:~coding_lt M(addM M i count)(code_numeral M 2)).
   { intro HBad. exact(HI(coding_le_lt_trans M i(addM M i count)(code_numeral M 2)(coding_le_add M i count) HBad)). }
   assert(EV:v=addM M(addM M i count) other).
   { eapply renaming_lookup_functional;[exact HV|apply representation_padding_outside_lookup;exact HJBound]. }
   subst v. unfold representation_padding_lookup. right. split;[exact HI|symmetry;apply Arithmetic.add_assoc].
Qed.
Definition source_representation_padding M count f g :=numerical_renaming M f
 (code_numeral M 6)(code_numeral M 2)(code_numeral M 2) count g.
Definition source_representation_padding_formula(count f g:term):form :=
 numerical_renaming_formula f(num 6)(num 2)(num 2) count g.
Theorem source_representation_padding_formula_correct M rho count f g :
 holds M rho(source_representation_padding_formula count f g) <->
 source_representation_padding M(evalM M rho count)(evalM M rho f)(evalM M rho g).
Proof. unfold source_representation_padding_formula,source_representation_padding.
 rewrite numerical_renaming_formula_correct. now repeat setoid_rewrite code_eval_num. Qed.
Theorem source_representation_padding_total M count f :exists g,source_representation_padding M count f g.
Proof. apply numerical_renaming_total. Qed.
Theorem source_representation_padding_functional M count f g h :
 source_representation_padding M count f g ->source_representation_padding M count f h ->g=h.
Proof. apply numerical_renaming_functional. Qed.
Theorem source_representation_padding_zero M f k :source_bounded M f k ->
 source_representation_padding M(zeroM M) f f.
Proof.
 intro HF. apply(numerical_renaming_identity_on_bound M f _ _ _ _ k HF).
 intros i _. destruct(environment_lt_cases M i(code_numeral M 2))as[HI|HI].
 - apply representation_padding_inside_lookup. exact HI.
 - pose proof(representation_padding_outside_lookup M(zeroM M) i HI)as H.
   now rewrite coding_add_zero_r in H.
Qed.
Theorem source_representation_padding_composition M count other f g h k :
 source_bounded M f k ->source_representation_padding M count f g ->
 source_representation_padding M other g h ->source_representation_padding M(addM M count other) f h.
Proof.
 intros HF HG HH. apply(representation_renaming_composition M f k _ _ _ _ _ _ _ _ _ _ _ _ g h HF HG HH).
 intros i j v _. apply representation_padding_lookup_composition.
Qed.
Theorem source_representation_padding_rotate_shift M f padded shifted rotated k :
 source_bounded M f k ->source_representation_padding M(code_numeral M 1) f padded ->
 source_formula_shift M f shifted ->
 numerical_renaming M padded(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) rotated ->
 rotated=shifted.
Proof.
 intros HF HP HS HR.
 assert(HShift:source_formula_shift M f rotated).
 { apply(representation_renaming_composition M f k _ _ _ _ _ _ _ _ _ _ _ _ padded rotated HF HP HR).
   intros i j v _ HJ HV. apply(proj2(context_shift_lookup M i v)).
   destruct(environment_lt_cases M i(code_numeral M 2))as[HI|HI].
   - assert(EJ:j=i)by(eapply renaming_lookup_functional;[exact HJ|apply representation_padding_inside_lookup;exact HI]). subst j.
     destruct(source_numeral_initial_segment M 2 i HI)as(index&HIndex&->).
     destruct index as[|[|index]];try lia.
     + exact(renaming_lookup_functional M _ _ _ _ _ _ _ HV(source_dn_rotate_zero M)).
     + exact(renaming_lookup_functional M _ _ _ _ _ _ _ HV(source_dn_rotate_one M)).
   - assert(EJ:j=succM M i).
     { pose proof(representation_padding_outside_lookup M(code_numeral M 1) i HI)as H.
       rewrite <-Arithmetic.succ_as_add in H. eapply renaming_lookup_functional;eassumption. }
     subst j. assert(HLarge:~coding_lt M(succM M i)(code_numeral M 3)).
     { intro HBad. apply HI. exact(proj1(coding_lt_succ_cancel M i(code_numeral M 2)) HBad). }
     exact(renaming_lookup_functional M _ _ _ _ _ _ _ HV(source_dn_rotate_outside M(succM M i) HLarge)). }
 exact(numerical_renaming_functional M f _ _ _ _ rotated shifted HShift HS).
Qed.
Print Assumptions representation_renaming_composition.
Print Assumptions source_representation_padding_formula_correct.
Print Assumptions source_representation_padding_composition.
Print Assumptions source_representation_padding_rotate_shift.
