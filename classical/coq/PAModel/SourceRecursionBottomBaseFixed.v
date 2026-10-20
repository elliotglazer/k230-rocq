(** Lift the fixed false-relation singleton attempt, identifying its exact source output. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge SourceLFixed SourceLNonempty
 OldZFRProofLift SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability SourceFiniteParameters SourceFiniteNameParameters
 SourceRecursionBottomBaseOld SourceRecursionBottomCalibration SourceRecursionPrimitiveRelations SourceRecursionParameterCalibration
 SourceRecursionStructureGraphs SourceRecursionInitialAttempt SourcePropositionalRebase SchemaConstructorBounds.
From OldZF Require Std_setrec Std_setbase Std_setinf.
Unset Implicit Arguments.
Definition source_rec_bottom_base_law:=isolated_formula old_recursion_bottom_base_law.
Theorem source_zfr_rec_bottom_base_named M rho out:
 code_relation M rho(source_parameter_expression(source_finite_parameter_names 3)source_rec_bottom_base_law)out ->source_zfr_provable M out.
Proof.
 intro HG. apply(proj1(source_zfr_descriptor_provable M out)).
 refine(source_descriptor_finite_parameter_proof M ZFRSourceDescriptor source_rec_bottom_base_law 3 rho out _ HG).
 apply(proj2(source_zfr_descriptor_provable M _)). exact(finite_old_zfr_proof_lift M old_L_background old_recursion_bottom_base_law old_L_background_valid old_recursion_bottom_base_proof).
Qed.
Theorem source_rec_bottom_base_shell M o a N law:
 code_relation M(source_rec_env3 o a N)(source_parameter_expression(source_finite_parameter_names 3)source_rec_bottom_base_law)law ->
 exists nonzero target,source_rec_nonzero M o N nonzero /\source_rec_initial_attempt M(zeroM M)o a N target /\sf_relation M SFImpl nonzero target law.
Proof.
 intro HG. set(rho:=source_rec_env3 o a N). set(names:=source_finite_parameter_names 3). set(up:=source_parameter_up names).
 set(NZ:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.SNz OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)))).
 set(ATT:=source_parameter_expression up(isolated_formula(OldZF.Std_setrec.Att OldZF.Std_setinf.phSig
  (@OC.falsity OB.sig_empty OS.ZFSignature.ZF_pred_sig OC.FullSyntax.full_operators)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 0)))).
 set(APP:=source_parameter_expression up(isolated_formula(OldZF.Std_setbase.App(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)))).
 change(code_relation M rho(E_sf SFImpl NZ(E_sf SFEx(E_sf SFAnd ATT APP)(CEconst 0)))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(nonzero&target&HNZ&HTarget&HImpl).
 pose proof(source_parameter_rec_nonzero M names rho 0 2 o N nonzero eq_refl eq_refl HNZ)as HNonzero.
 destruct(schema_expression_split M rho SFEx(E_sf SFAnd ATT APP)(CEconst 0)target HTarget)as(body&z0&HBody&HZ&HEx). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAnd ATT APP body HBody)as(att&app&HAtt&HApp&HAnd).
 assert(U0:code_relation M rho(up 0)(zeroM M))by reflexivity.
 assert(U1:code_relation M rho(up 1)(succM M o))by(apply(source_parameter_up_name M names rho 0 o);reflexivity).
 assert(U2:code_relation M rho(up 2)(succM M a))by(apply(source_parameter_up_name M names rho 1 a);reflexivity).
 assert(U3:code_relation M rho(up 3)(succM M N))by(apply(source_parameter_up_name M names rho 2 N);reflexivity).
 pose proof(source_parameter_rec_bottom_attempt M up rho 1 2 3 0 _ _ _ _ att U1 U2 U3 U0 HAtt)as HAttGraph.
 pose proof(source_parameter_rec_app M up rho 0 1 2 _ _ _ app U0 U1 U2 HApp)as HAppGraph.
 exists nonzero,target. split;[exact HNonzero|]. split;[exists att,app,body;auto|exact HImpl].
Qed.
Theorem source_zfr_rec_bottom_base_total M o a N:exists nonzero target law,
 source_rec_nonzero M o N nonzero /\source_rec_initial_attempt M(zeroM M)o a N target /\sf_relation M SFImpl nonzero target law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)source_rec_bottom_base_law)(source_rec_env3 o a N))as(law&HG).
 destruct(source_rec_bottom_base_shell M o a N law HG)as(nonzero&target&HN&HT&HI).
 exists nonzero,target,law. split;[exact HN|]. split;[exact HT|]. split;[exact HI|]. exact(source_zfr_rec_bottom_base_named M(source_rec_env3 o a N)law HG).
Qed.
Print Assumptions source_zfr_rec_bottom_base_named.
Print Assumptions source_rec_bottom_base_shell.
Print Assumptions source_zfr_rec_bottom_base_total.
