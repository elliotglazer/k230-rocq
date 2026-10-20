(** Fixed role syntax used by the fresh-witness EnvF domain induction. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded
 SourceEnvFDomainWitnessOld SourceEnvFDomainWitnessTransport SourceEnvFDomainWitnessRecipe
 SourceDefinabilityPrimitives SourceDefinabilityIteration SourceDefinabilityBounds SourceDefinabilityLogicalStep
 SourceNumFUniqueSyntax SourceNumFUniqueFiniteShells SourceEnvFDomainGraph SourceEnvFDomainFixed
 SourceFiniteCutoffShift NumericalSubstitutionMaps NumericalSubstitution NumericalRenaming RenamingSubstitution SourceQuantifierRules
 OldNamedSyntaxBridge OldFullNDSourceBridge OldZFRProofLift SourceLFixed SourceLNonempty SourceZFRProvability.
From OldZFC Require Z_cl Z_base.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition ew_domain(e d:nat):sf_form:=isolated_formula(OldZFC.Z_base.Dom0(@OC.var OB.sig_empty e)(@OC.var OB.sig_empty d)).
Definition ew_domain_code M e d:=code_numeral M(sf_encode(ew_domain e d)).
Definition ew_extension032:sf_form:=source_def_extension021[source_shift_sigma 1].
Definition ew_extension143:sf_form:=ew_extension032[↑].
Lemma ew_extension032_shape:ew_extension032=isolated_formula(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 2)).
Proof.
 unfold ew_extension032,source_def_extension021.
 pose proof(isolated_formula_subst(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 1))
  (fun idx=>match idx with 0=>@OC.var OB.sig_empty 0|S j=>@OC.var OB.sig_empty(S(S j))end)
  (source_shift_sigma 1)ltac:(intros[|idx];reflexivity))as E.
 rewrite OldZFC.Z_cl.Ext0_subst in E. exact(eq_sym E).
Qed.
Lemma ew_extension143_shape:ew_extension143=isolated_formula(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 3)).
Proof.
 unfold ew_extension143. rewrite ew_extension032_shape.
 pose proof(isolated_old_formula_shift(OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 2)))as E.
 rewrite OldZFC.Z_cl.Ext0_subst in E. exact(eq_sym E).
Qed.
Definition ew_empty_law:=isolated_formula old_env_domain_witness_empty_law.
Definition ew_extension_law:=isolated_formula old_env_domain_witness_extension_law.
Lemma ew_empty_law_shape:ew_empty_law=(source_def_empty[↑]→source_def_empty→ew_domain 1 0).
Proof. rewrite numf_empty_shift_shape. reflexivity. Qed.
Lemma ew_extension_law_shape:ew_extension_law=(ew_domain 1 0→numf_successor02→ew_extension143→ew_domain 3 2).
Proof. rewrite numf_successor02_shape,ew_extension143_shape. reflexivity. Qed.
Theorem source_zfr_ew_empty_fixed M:source_zfr_provable M(code_numeral M(sf_encode ew_empty_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_env_domain_witness_empty_law old_L_background_valid old_env_domain_witness_empty_proof). Qed.
Theorem source_zfr_ew_extension_fixed M:source_zfr_provable M(code_numeral M(sf_encode ew_extension_law)).
Proof. exact(finite_old_zfr_proof_lift M old_L_background old_env_domain_witness_extension_law old_L_background_valid old_env_domain_witness_extension_proof). Qed.
Local Opaque code_numeral source_def_empty ew_domain ew_extension143 numf_successor02.
Theorem source_zfr_ew_extension_shell M:exists tail middle law,
 sf_relation M SFImpl(code_numeral M(sf_encode ew_extension143))(ew_domain_code M 3 2)tail /\
 sf_relation M SFImpl(code_numeral M(sf_encode numf_successor02))tail middle /\
 sf_relation M SFImpl(ew_domain_code M 1 0)middle law /\source_zfr_provable M law.
Proof.
 set(d:=sf_encode(ew_domain 1 0)). set(s:=sf_encode numf_successor02).
 set(e:=sf_encode ew_extension143). set(o:=sf_encode(ew_domain 3 2)).
 set(t:=sf_make SFImpl e o). set(m:=sf_make SFImpl s t). set(l:=sf_make SFImpl d m).
 exists(code_numeral M t),(code_numeral M m),(code_numeral M l).
 split;[apply sf_make_numeral|]. split;[apply sf_make_numeral|]. split;[apply sf_make_numeral|].
 pose proof(source_zfr_ew_extension_fixed M)as P. rewrite ew_extension_law_shape in P. exact P.
Qed.
Theorem source_zfr_env_domain_witness_empty M out:
 source_env_domain_witness_recipe M(code_numeral M(sf_encode source_def_empty))(code_numeral M(sf_encode source_def_empty))out->source_zfr_provable M out.
Proof.
 intro H. set(p:=sf_encode source_def_empty). set(q:=sf_encode(source_def_empty[↑])). set(d:=sf_encode(ew_domain 1 0)).
 set(i:=sf_make SFImpl p d). set(o:=sf_make SFImpl q i).
 assert(HCanon:source_env_domain_witness_recipe M(code_numeral M p)(code_numeral M p)(code_numeral M o)).
 { exists(code_numeral M q),(code_numeral M d),(code_numeral M i).
   split;[apply source_formula_numeral_shift|]. split;[exact(source_env_domain_old_numeral M 1 0)|]. split;apply sf_make_numeral. }
 rewrite(source_env_domain_witness_recipe_functional M _ _ out(code_numeral M o)H HCanon).
 pose proof(source_zfr_ew_empty_fixed M)as P. rewrite ew_empty_law_shape in P. exact P.
Qed.
Theorem source_zfr_env_domain_witness_zero M:source_env_domain_witness_proof_at M(zeroM M).
Proof.
 intros environment numeral out HE HN HO. apply source_def_iteration_zero in HE,HN. subst environment numeral.
 exact(source_zfr_env_domain_witness_empty M out HO).
Qed.
Print Assumptions source_zfr_ew_extension_shell.
Print Assumptions source_zfr_env_domain_witness_empty.
Print Assumptions source_zfr_env_domain_witness_zero.
