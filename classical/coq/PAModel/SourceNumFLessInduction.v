(** Uniform internally indexed membership proofs, by genuine PA induction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift NumericalProofs
 SourceDefinabilityBounds SourceDefinabilityIteration SourceDefinabilityPrimitives SourceDefinabilityStep SourceDefinabilityLogicalStep SourceNumFUniqueNames
 SourceNumFLessProofProperty SourceNumFLessNames SourceNumFLessStepCore SourceNumFLessFacts
 SourceNumFLessRecipe SourceNumFUniqueSyntax NumericalInstantiation NumericalRenaming SourceZFRProvability.
Unset Implicit Arguments.
Theorem source_zfr_numf_less_successor M l :source_numf_less_proof_at M l ->source_numf_less_proof_at M(succM M l).
Proof.
 intros IH k r q x y out HK HR HQ HO.
 apply source_def_iteration_succ in HQ. destruct HQ as(p&HP&HStep).
 pose proof(source_numf_bound M k r HR)as BR.
 pose proof(source_numf_bound M l p HP)as BP.
 pose proof(source_def_numeral_step_bound M p q BP HStep)as BQ.
 destruct(numerical_renaming_total M r(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(rs&HRS).
 destruct(source_numf_less_recipe_total M r q(zeroM M)(code_numeral M 1))as(canonical&HC).
 assert(PC:source_zfr_provable M canonical).
 { destruct(proj1(coding_lt_succ_cases M k l)HK)as[HKL|E].
   - destruct(sf_relation_total M SFImpl p(numf_comparison_atom M false))as(ri&HRI).
     destruct(sf_relation_total M SFImpl rs ri)as(law&HL).
     assert(HRecipe:source_numf_less_recipe M r p(code_numeral M 1)(zeroM M)law).
     { exists rs,p,(numf_comparison_atom M false),ri. repeat split.
       - exact(source_unit_instantiation_shift M r rs BR HRS).
       - exact(source_unit_instantiation_self M p BP).
       - exact(sf_make_numeral M SFMember 1 0).
       - exact HRI.
       - exact HL. }
     exact(source_zfr_numf_less_step_core M false r p q rs ri law canonical BR BP HStep HRS HRI HL
       (IH k r p(code_numeral M 1)(zeroM M)law HKL HR HP HRecipe)HC).
   - subst k. assert(E:r=p)by(eapply source_def_iteration_functional;[exact HR|exact HP]). subst r.
     destruct(sf_relation_total M SFImpl p(numf_comparison_atom M true))as(ri&HRI).
     destruct(sf_relation_total M SFImpl rs ri)as(law&HL).
     pose proof(source_zfr_numf_unique_names M l p(code_numeral M 1)(zeroM M)rs p(numf_comparison_atom M true)ri law
       HP(source_unit_instantiation_shift M p rs BP HRS)(source_unit_instantiation_self M p BP)
       (sf_make_numeral M SFEqual 1 0)HRI HL)as PL.
     exact(source_zfr_numf_less_step_core M true p p q rs ri law canonical BP BP HStep HRS HRI HL PL HC). }
 exact(source_zfr_numf_less_recipe_names M r q canonical x y out BR BQ HC PC HO).
Qed.
Theorem source_zfr_numf_less_uniform M :forall l,source_numf_less_proof_at M l.
Proof.
 apply(definable_induction M(source_numf_less_proof_at M)(source_numf_less_proof_definable M)).
 - intros k p q x y out HK. exfalso. exact(coding_not_lt_zero M k HK).
 - exact(source_zfr_numf_less_successor M).
Qed.
Theorem source_zfr_numf_less_total M k l x y :coding_lt M k l ->exists p q out,
 source_numf M k p /\source_numf M l q /\source_numf_less_recipe M p q x y out /\source_zfr_provable M out.
Proof.
 intro HK. destruct(source_numf_total M k)as(p&HP). destruct(source_numf_total M l)as(q&HQ).
 destruct(source_numf_less_recipe_total M p q x y)as(out&HO).
 exists p,q,out. repeat split;try assumption. exact(source_zfr_numf_less_uniform M l k p q x y out HK HP HQ HO).
Qed.
Print Assumptions source_zfr_numf_less_successor.
Print Assumptions source_zfr_numf_less_uniform.
Print Assumptions source_zfr_numf_less_total.
