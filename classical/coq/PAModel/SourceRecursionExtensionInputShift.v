(** Genuine ordinary shifts of the finite extension-premise tuple. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules SourceImplicationAllShift
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport
 SourceRecursionExtensionInputs SourceRecursionPrimitiveShifts SourceRecursionShiftGraphs SourceRecursionAtomicShift SourceRecursionSetOperationTransport.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_rec_app_shift M f u v old new:
 source_rec_app M f u v old ->source_rec_app M(succM M f)(succM M u)(succM M v)new ->source_formula_shift M old new.
Proof.
 intros HO HN. apply(proj2(numerical_renaming_substitution M old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)new)).
 rewrite Arithmetic.add_zero. exact(source_rec_app_substitution M f u v old(succM M f)(succM M u)(succM M v)new
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)HO HN(source_rec_shift_lookup M f)(source_rec_shift_lookup M u)(source_rec_shift_lookup M v)).
Qed.
Theorem source_rec_extension_inputs_shift M phi o a N f q g z next p w A AS:
 source_bounded M phi(code_numeral M 2) ->source_rec_extension_inputs M phi o a N f q g z next p w A ->
 source_rec_extension_inputs M phi(succM M o)(succM M a)(succM M N)(succM M f)(succM M q)(succM M g)(succM M z)(succM M next)(succM M p)(succM M w)AS ->
 Forall2(source_formula_shift M)A AS.
Proof.
 intros BP(inj&att&mz&sz&appf&adj&op&binary&E&HI&HT&HMZ&HSZ&HAF&HA&HO&HG)
  (inj'&att'&mz'&sz'&appf'&adj'&op'&binary'&E'&HI'&HT'&HMZ'&HSZ'&HAF'&HA'&HO'&HG'). subst A AS.
 constructor;[exact(source_rec_injectivity_shift M N inj inj' HI HI')|].
 constructor;[exact(source_rec_attempt_shift M phi o a N f att att' BP HT HT')|].
 constructor;[exact(source_rec_member_shift M z N mz mz' HMZ HMZ')|].
 constructor;[exact(source_rec_successor_shift M z next sz sz' HSZ HSZ')|].
 constructor;[exact(source_rec_app_shift M f z p appf appf' HAF HAF')|].
 constructor;[exact(source_rec_adjoin_shift M f q g adj adj' HA HA')|].
 constructor;[exact(source_rec_ordered_pair_shift M next w q op op' HO HO')|].
 constructor;[exact(source_rec_binary_shift M phi p w binary binary' BP HG HG')|constructor].
Qed.
Theorem source_finite_shifted_bounds M A AS k:
 Forall2(source_formula_shift M)A AS ->(forall a,In a A ->source_bounded M a k) ->forall a,In a AS ->source_bounded M a(succM M k).
Proof.
 intro H. induction H;intros BA a HA;[contradiction|]. destruct HA as[<-|HA].
 - exact(source_shift_bound M x y k(BA x(or_introl eq_refl))H).
 - exact(IHForall2(fun z HZ=>BA z(or_intror HZ))a HA).
Qed.
Print Assumptions source_rec_app_shift.
Print Assumptions source_rec_extension_inputs_shift.
Print Assumptions source_finite_shifted_bounds.
