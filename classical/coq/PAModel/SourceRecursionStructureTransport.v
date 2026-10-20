(** Arbitrary numerical substitution of the seven recursion hypotheses. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution SourceSubstitutionIdentity SchemaRenamingDescriptors
 SourceRecursionStructureInputs SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionTotalRelation
 SourceRecursionTotalFunctional SourceRecursionNonzeroTransport SourceRecursionPrimitiveShifts
 SourceRecursionInductionTransport SourceRecursionInductionShift.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_rec_structure_inputs_substitution M phi o N A o' N' B rb rc rn base:
 source_bounded M phi(code_numeral M 2) ->source_rec_structure_inputs M phi o N A ->source_rec_structure_inputs M phi o' N' B ->
 substitution_lookup M rb rc rn base o o' ->substitution_lookup M rb rc rn base N N' ->
 Forall2(fun x y=>numerical_substitution M x rb rc rn base y)A B.
Proof.
 intros BP(funlaw&totalG&nonzero&injective&totality&induction&member&E&HFun&HG&HNZ&HInj&HT&HI&HM)
 (funlaw'&totalG'&nonzero'&injective'&totality'&induction'&member'&E'&HFun'&HG'&HNZ'&HInj'&HT'&HI'&HM')HO HN. subst A B.
 pose proof(source_rec_total_relation_functional M phi totalG' totalG HG' HG)as EQ. subst totalG'.
 destruct HFun as(ra&rb'&HRA&HRB&HFun). destruct HFun' as(ra'&rb''&HRA'&HRB'&HFun').
 pose proof(schema_renaming_functional M RepA phi ra' ra HRA' HRA)as EQ. subst ra'.
 pose proof(schema_renaming_functional M RepB phi rb'' rb' HRB' HRB)as EQ. subst rb''.
 pose proof(code_relation_functional M _ _ funlaw' funlaw HFun' HFun)as EQ. subst funlaw'.
 assert(HFunctionality:source_rec_functionality M phi funlaw)by(exists ra,rb';auto).
 constructor.
 - apply(numerical_substitution_identity_on_bound M funlaw rb rc rn base(zeroM M)(source_rec_functionality_closed M phi funlaw BP HFunctionality)).
   intros i Hlt. exfalso. exact(coding_not_lt_zero M i Hlt).
 - constructor.
   + apply(numerical_substitution_identity_on_bound M totalG rb rc rn base(zeroM M)(source_rec_total_relation_closed M phi totalG BP HG)).
     intros i Hlt. exfalso. exact(coding_not_lt_zero M i Hlt).
   + constructor;[exact(source_rec_nonzero_substitution M o N nonzero o' N' nonzero' rb rc rn base HNZ HNZ' HO HN)|].
     constructor;[exact(source_rec_injectivity_substitution M N injective N' injective' rb rc rn base HInj HInj' HN)|].
     constructor;[exact(source_rec_totality_substitution M N totality N' totality' rb rc rn base HT HT' HN)|].
     constructor;[exact(source_rec_induction_substitution M o N induction o' N' induction' rb rc rn base HI HI' HO HN)|].
     constructor;[|constructor].
     apply(proj2(numerical_substitution_member M o N member rb rc rn base member' HM)).
     exists o',N'. auto.
Qed.
Print Assumptions source_rec_structure_inputs_substitution.
