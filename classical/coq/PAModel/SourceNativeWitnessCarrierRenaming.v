(** Actual native witness_closed graph under a fresh carrier renaming.
 The arbitrary matrix code is kept fixed by its checked twice-lifted map. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceFiniteCutoffShift
 SourceUpperWitnessRecipes SourceNativeCarrierMatrix SourceZeroTransposition NumericalRenamingMaps NumericalRenaming
 SourceFiniteParameters SourceFiniteParameterProofs SourceParameterTransport SourceSubsetClosedPoint SourceSubsetClosedShift
 SourceUpperTraceFrame RenamingSubstitution.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_upper_witness_matrix_renaming M matrix carrier raw carrier' out b c n delta r1 r2 n1 s1 s2 n2:
 code_relation M(SetSchemaConstructors.schema_env3 matrix carrier carrier)(E_upper_witness_closed(CEvar 0)(CEvar 1))raw->
 code_relation M(SetSchemaConstructors.schema_env3 matrix carrier' carrier')(E_upper_witness_closed(CEvar 0)(CEvar 1))out->
 renaming_lookup M b c n delta carrier carrier'->renaming_lift M b c n delta r1 r2 n1->
 renaming_lift M r1 r2 n1 delta s1 s2 n2->numerical_renaming M matrix s1 s2 n2 delta matrix->
 numerical_renaming M raw b c n delta out.
Proof.
 intros HRaw HOut HCarrier HL1 HL2 HMatrix.
 destruct(source_upper_witness_closed_shell M matrix carrier raw HRaw)as(g&m&pair&some&bounded&request&point&HG&HM&HPair&HSome&HBounded&HRequest&HPoint&HAll).
 destruct(source_upper_witness_closed_shell M matrix carrier' out HOut)as(g'&m'&pair'&some'&bounded'&request'&point'&HG'&HM'&HPair'&HSome'&HBounded'&HRequest'&HPoint'&HAll').
 apply(proj2(numerical_renaming_quantifier M true point raw b c n delta out HAll)).
 exists r1,r2,n1,point'. split;[exact HL1|]. split;[|exact HAll'].
 apply(proj2(numerical_renaming_binary M SFImpl g request point r1 r2 n1 delta point'(or_intror(or_intror eq_refl))HPoint)).
 exists g',request'. split.
 - apply(proj2(numerical_renaming_member M(zeroM M)(succM M carrier)g r1 r2 n1 delta g' HG)).
   exists(zeroM M),(succM M carrier'). split;[exact(proj1(proj2 HL1))|]. split;[exact(proj2(proj2 HL1)carrier carrier' HCarrier)|exact HG'].
 - split;[|exact HPoint']. apply(proj2(numerical_renaming_binary M SFImpl some bounded request r1 r2 n1 delta request'
    (or_intror(or_intror eq_refl))HRequest)). exists some',bounded'. split.
   + apply(proj2(numerical_renaming_quantifier M false matrix some r1 r2 n1 delta some' HSome)).
     exists s1,s2,n2,matrix. auto.
   + split;[|exact HRequest']. apply(proj2(numerical_renaming_quantifier M false pair bounded r1 r2 n1 delta bounded' HBounded)).
     exists s1,s2,n2,pair'. split;[exact HL2|]. split;[|exact HBounded'].
     apply(proj2(numerical_renaming_binary M SFAnd m matrix pair s1 s2 n2 delta pair'(or_introl eq_refl)HPair)).
     exists m',matrix. split;[|auto].
     apply(proj2(numerical_renaming_member M(zeroM M)(succM M(succM M carrier))m s1 s2 n2 delta m' HM)).
     exists(zeroM M),(succM M(succM M carrier')). split;[exact(proj1(proj2 HL2))|]. split;[|exact HM'].
     exact(proj2(proj2 HL2)(succM M carrier)(succM M carrier')(proj2(proj2 HL1)carrier carrier' HCarrier)).
Qed.
Theorem source_native_witness_carrier_transposition M phi shifted n fresh b c raw out:
 source_bounded M phi(succM M(succM M n))->source_cutoff_shift M 2 phi shifted->
 coding_lt M(succM M(succM M n))fresh->source_zero_transposition M fresh b c->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)(zeroM M)raw->
 source_upper_witness_closed_recipe M shifted(code_numeral M 1)fresh out->
 numerical_renaming M raw b c(succM M fresh)(zeroM M)out.
Proof.
 intros BP HCut HF HTrans(mat&HMat&HRaw)(mat'&HMat'&HOut).
 pose proof(numerical_renaming_functional M shifted _ _ _ _ mat mat' HMat HMat')as E;subst mat'.
 destruct(renaming_lift_total M b c(succM M fresh)(zeroM M))as(r1&r2&n1&HL1).
 destruct(renaming_lift_total M r1 r2 n1(zeroM M))as(s1&s2&n2&HL2).
 exact(source_upper_witness_matrix_renaming M mat(zeroM M)raw fresh out b c(succM M fresh)(zeroM M)r1 r2 n1 s1 s2 n2
  HRaw HOut(source_zero_transposition_zero M fresh b c HTrans)HL1 HL2
  (source_native_witness_matrix_carrier_fixed M phi shifted mat(succM M(succM M n))fresh b c r1 r2 n1 s1 s2 n2 BP HF HCut HMat HTrans HL1 HL2)).
Qed.
Theorem source_subset_closed_carrier_renaming M carrier raw carrier' out b c n delta:
 source_subset_closed_graph M carrier raw->source_subset_closed_graph M carrier' out->
 renaming_lookup M b c n delta carrier carrier'->numerical_renaming M raw b c n delta out.
Proof.
 intros HRaw HOut HName. apply(proj2(numerical_renaming_substitution M raw b c n delta out)).
 apply(source_parameter_transport M 1(source_point_subset_closed(Undecidability.FOL.Syntax.Core.var 0))
  source_point_subset_closed_bound source_three_parameter_names source_three_parameter_names(fun _=>carrier)(fun _=>carrier')
  b c n(Model.addM M n delta)raw out);[|exact HRaw|exact HOut].
 intros[|i]x y HI HX HY;[|lia]. change(x=carrier)in HX. change(y=carrier')in HY. subst x y.
 exact(proj1(renaming_substitution_lookup M b c n delta carrier carrier')HName).
Qed.
Print Assumptions source_upper_witness_matrix_renaming.
Print Assumptions source_native_witness_carrier_transposition.
Print Assumptions source_subset_closed_carrier_renaming.
