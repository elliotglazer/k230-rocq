(** The genuine generic recursion kernel at arbitrary model-valued names. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceFiniteNameParameters NumericalRenaming NumericalRenamingMaps NumericalSubstitutionMaps
 NumericalSubstitution RenamingSubstitution SourceFiniteTelescope SourceFiniteTelescopeTransport
 SourceRecursionStructureInputs SourceRecursionStructureTransport SourceRecursionClosureExists
 SourceRecursionClosureTheorem SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.
Theorem source_zfr_rec_closure_named_theorem M phi o a N A target law:
 source_bounded M phi(code_numeral M 2) ->source_rec_structure_inputs M phi o N A ->
 source_rec_closure_exists M phi a target ->source_finite_telescope M A target law ->source_zfr_provable M law.
Proof.
 intros BP HA HT HL.
 destruct(source_rec_structure_inputs_total M phi(code_numeral M 0)(code_numeral M 2))as(C&HC).
 destruct(source_rec_closure_exists_total M phi(code_numeral M 1))as(ct&HCT).
 destruct(source_finite_telescope_total M C ct)as(cl&HCL).
 pose proof(source_zfr_rec_closure_theorem M phi C ct cl BP HC HCT HCL)as PC.
 destruct(source_finite_names_total M 3(fun i=>match i with 0=>o|1=>a|_=>N end)(zeroM M))as(rb&rc&HNames).
 pose proof(proj1(renaming_substitution_lookup M rb rc(code_numeral M 3)(zeroM M)(code_numeral M 0)o)(HNames 0 ltac:(lia)))as HO.
 pose proof(proj1(renaming_substitution_lookup M rb rc(code_numeral M 3)(zeroM M)(code_numeral M 1)a)(HNames 1 ltac:(lia)))as HInitial.
 pose proof(proj1(renaming_substitution_lookup M rb rc(code_numeral M 3)(zeroM M)(code_numeral M 2)N)(HNames 2 ltac:(lia)))as HN.
 pose proof(source_rec_structure_inputs_substitution M phi(code_numeral M 0)(code_numeral M 2)C o N A
  rb rc(code_numeral M 3)(addM M(code_numeral M 3)(zeroM M))BP HC HA HO HN)as HS.
 pose proof(source_rec_closure_exists_substitution M phi(code_numeral M 1)ct a target
  rb rc(code_numeral M 3)(addM M(code_numeral M 3)(zeroM M))BP HCT HT HInitial)as HSubTarget.
 pose proof(source_finite_telescope_substitution M C A ct target cl law rb rc(code_numeral M 3)
  (addM M(code_numeral M 3)(zeroM M))HS HSubTarget HCL HL)as HSub.
 apply(proj1(source_zfr_descriptor_provable M law)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor cl rb rc(code_numeral M 3)(zeroM M)law
  (proj2(source_zfr_descriptor_provable M cl)PC)
  (proj2(numerical_renaming_substitution M cl rb rc(code_numeral M 3)(zeroM M)law)HSub)).
Qed.
Print Assumptions source_zfr_rec_closure_named_theorem.
