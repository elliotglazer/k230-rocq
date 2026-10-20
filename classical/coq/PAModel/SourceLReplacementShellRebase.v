(** Exact finite shell rebasing for the L Replacement proof. These
    identities contain only arithmetic syntax graphs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions ProofTemplates SetFormulaCodes SetSchemaConstructors
 QuotationSchemaSkeleton SourceSchemaRelativization SourceRelativeSchemaConstructors SourceWFReplacementConstructor SourceFunctionalityShells SourcePropositionalRebase
 SourceWFSeparationConstructor SourceLReplacementPsiR SourceLReplacementCutShells SourceLReplacementBoundCut.
Unset Implicit Arguments.
Theorem source_L_separation_law_rebase M domain matrix out:
 sf_relative_separation_constructor M domain matrix out <->
 code_relation M(schema_env3 domain matrix(zeroM M))(E_L_separation_law(CEvar 0)(CEvar 1))out.
Proof.
 unfold sf_relative_separation_constructor. rewrite relative_separation_skeleton_exact.
 exact(Logic.iff_sym(code_subst_graph M(schema_env3 domain matrix(zeroM M))
  (fun i=>match i with 0=>CEvar 0|_=>CEvar 1 end)
  (skeleton_relative_environment domain(fun _=>matrix))ltac:(intros[|i];reflexivity)
   (E_sf_relative_separation(CEvar 0)(CEvar 1))out)).
Qed.
Theorem source_L_replacement_open_split M domain ra rb rc theta target:
 code_relation M(schema_env3 domain rc(zeroM M))(E_L_replacement_theta(CEvar 0)(CEvar 1))theta ->
 sf_relative_replacement_constructor M domain ra rb rc target ->
 exists functor rhs guarded witness,
 source_relative_functionality_graph M domain ra rb functor /\
 sf_relation M SFImpl functor rhs target /\sf_relation M SFAll guarded(zeroM M)rhs /\
 sf_relation M SFImpl domain witness guarded /\
 code_relation M(schema_env3 domain theta(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))witness.
Proof.
 intros HTheta HTarget. unfold sf_relative_replacement_constructor in HTarget.
 rewrite relative_replacement_skeleton_exact in HTarget. unfold E_sf_relative_replacement in HTarget.
 destruct(schema_expression_split M _ SFImpl _ _ target HTarget)as(functor&rhs&HFunctor&HRhs&HImp).
 pose proof(source_replacement_relative_functionality_rebase M domain ra rb rc functor HFunctor)as HFunc.
 unfold E_sf_relative_all,E_sf_all in HRhs.
 destruct(schema_expression_quantifier_split M _ SFAll _ rhs HRhs)as(guarded&HGuarded&HAll).
 destruct(schema_expression_split M _ SFImpl _ _ guarded HGuarded)as(d&witness&HD&HWitness&HGuard).
 change(d=domain)in HD. subst d.
 assert(HWitness':code_relation M(schema_env3 domain theta(zeroM M))(E_L_cut_witness(CEvar 0)(CEvar 1))witness).
 { apply(proj1(code_subst_graph M(skeleton_relative_environment domain(schema_env3 ra rb rc))
   (fun i=>match i with 0=>CEvar 0|1=>E_L_replacement_theta(CEvar 0)(CEvar 3)|_=>CEconst 0 end)
   (schema_env3 domain theta(zeroM M))ltac:(intros[|[|i]];try reflexivity;exact HTheta)
   (E_L_cut_witness(CEvar 0)(CEvar 1))witness)). exact HWitness. }
 exists functor,rhs,guarded,witness. repeat split;assumption.
Qed.
Print Assumptions source_L_separation_law_rebase.
Print Assumptions source_L_replacement_open_split.

