(** The exact relative psiR image has the Replacement witness predicate
    after one carrier insertion. All matrices and bounds are internal. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceLMatrixRecipes SourceRelativization SourceRelativizationFunctionality SourceRelativizationRules
 SourceLSeparationMatrixShift SourceCutoffShiftConstructors SourceCutoffQuantifiers SourceCutoffPropositional
 SourceFiniteCutoffShift SourceQfFunctionality SetSchemaConstructors SourcePropositionalRebase SourceWFSeparationConstructor.
Unset Implicit Arguments.
Definition E_L_replacement_theta domain matrix :=
 E_sf_ex(E_sf SFAnd domain(E_sf SFAnd(E_sf_mem 0 3)matrix)).
Theorem source_L_psiR_relative_cutoff M domain phi psi rphi rpsi first second theta:
 source_bounded M domain(code_numeral M 1) ->source_l_psiR M phi psi ->
 source_relativization M domain phi rphi ->source_relativization M domain psi rpsi ->
 source_cutoff_shift M 2 rphi first ->source_cutoff_shift M 2 first second ->
 code_relation M(schema_env3 domain second(zeroM M))
   (E_L_replacement_theta(CEvar 0)(CEvar 1))theta ->
 source_cutoff_shift M 1 rpsi theta.
Proof.
 intros HD(shifted&atom&body&HShift&HAtom&HBody&HEx)HRPhi HRPsi HFirst HSecond HTheta.
 destruct(source_relativization_quantifier_inv M domain false body psi rpsi HEx HRPsi)
  as(relative&HRelative&HQuant).
 destruct(source_relativization_binary_inv M domain SFAnd atom shifted body relative(or_introl eq_refl)HBody HRelative)
  as(ra&rs&HRA&HRS&HAnd).
 assert(E:ra=atom)by(exact(source_relativization_atom_inv M domain false(zeroM M)(code_numeral M 2)atom ra HAtom HRA)).
 subst ra.
 pose proof(source_cutoff_relativization_to M 2 domain phi shifted rphi rs HD HShift HRPhi HRS)as HRSShift.
 assert(E:rs=first)by(exact(source_cutoff_shift_functional M 2 rphi rs first HRSShift HFirst)). subst rs.
 destruct HQuant as(guard&HGuard&HOut).
 unfold E_L_replacement_theta,E_sf_ex in HTheta.
 destruct(schema_expression_quantifier_split M _ SFEx _ theta HTheta)as(targetbody&HTargetBody&HTargetEx).
 destruct(schema_expression_split M _ SFAnd _ _ targetbody HTargetBody)as(d&targetand&HDCode&HTargetAnd&HTargetGuard).
 change(d=domain)in HDCode. subst d.
 destruct(schema_expression_split M _ SFAnd _ _ targetand HTargetAnd)as(targetatom&matrix&HTargetAtom&HMatrix&HTargetPair).
 change(matrix=second)in HMatrix. subst matrix.
 change(sf_relation M SFMember(zeroM M)(code_numeral M 3)targetatom)in HTargetAtom.
 pose proof(source_cutoff_shift_fixed_member M 2 0 2 atom targetatom HAtom HTargetAtom)as HAtomShift.
 pose proof(source_cutoff_shift_binary M 2 SFAnd atom first relative targetatom second targetand
  (or_introl eq_refl)HAnd HTargetPair HAtomShift HSecond)as HAndShift.
 pose proof(source_cutoff_shift_binary M 2 SFAnd domain relative guard domain targetand targetbody
  (or_introl eq_refl)HGuard HTargetGuard(source_cutoff_shift_fixes_domain M 1 domain HD)HAndShift)as HGuardShift.
 exact(source_cutoff_quantifier_join M 1 false guard targetbody rpsi theta HOut HTargetEx HGuardShift).
Qed.
Print Assumptions source_L_psiR_relative_cutoff.

