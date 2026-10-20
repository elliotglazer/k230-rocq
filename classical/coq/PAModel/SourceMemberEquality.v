(** Actual ZFR membership transport at three arbitrary model-valued
    source names.  The finite certificate is first lifted and then
    renamed by an internally coded map. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceMemberEqualityOld SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift
  SourceFiniteParameters SourceFiniteParameterProofs SourceZFRProvability
  SourceDescriptorProvability SourceSetTheoryDescriptors SetSchemaConstructors
  SchemaConstructorBounds SourcePropositionalRebase.
Unset Implicit Arguments.

Definition source_member_right_equality_law :=isolated_formula old_member_right_equality_law.
Definition source_member_right_equality_expression :=
  source_parameter_expression source_three_parameter_names source_member_right_equality_law.

Theorem source_zfr_member_right_equality M rho out :
  code_relation M rho source_member_right_equality_expression out ->source_zfr_provable M out.
Proof.
  intro HO. apply(proj1(source_zfr_descriptor_provable M out)).
  apply(source_descriptor_three_parameter_proof M ZFRSourceDescriptor
    source_member_right_equality_law rho out).
  - apply(proj2(source_zfr_descriptor_provable M _)).
    exact(finite_old_zfr_proof_lift M old_L_background old_member_right_equality_law
      old_L_background_valid old_member_right_equality_proof).
  - exact HO.
Qed.

Theorem source_member_right_equality_shell M rho out :
  code_relation M rho source_member_right_equality_expression out ->
  exists equal memberOld memberNew implication,
    sf_relation M SFEqual (rho 1)(rho 2) equal /\
    sf_relation M SFMember (rho 0)(rho 1) memberOld /\
    sf_relation M SFMember (rho 0)(rho 2) memberNew /\
    sf_relation M SFImpl memberOld memberNew implication /\
    sf_relation M SFImpl equal implication out.
Proof.
  intro HO.
  change(code_relation M rho(E_sf SFImpl(E_sf SFEqual(CEvar 1)(CEvar 2))
    (E_sf SFImpl(E_sf SFMember(CEvar 0)(CEvar 1))(E_sf SFMember(CEvar 0)(CEvar 2)))) out) in HO.
  destruct(schema_expression_split M rho SFImpl _ _ out HO) as (equal&implication&HE&HI&HOut).
  destruct(schema_expression_split M rho SFImpl _ _ implication HI) as (memberOld&memberNew&HM&HN&HImp).
  exists equal,memberOld,memberNew,implication. repeat split;assumption.
Qed.

Print Assumptions source_zfr_member_right_equality.
Print Assumptions source_member_right_equality_shell.
