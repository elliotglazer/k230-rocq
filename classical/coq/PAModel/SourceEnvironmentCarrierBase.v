(** Actual base case for carriers of EnvF environments. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceEnvironmentCarrierRecipe SourceEnvironmentCarrierClosure SourceEnvironmentCarrierOld SourceEnvironmentCarrierFixed
 SourceDefinabilityPrimitives SourceDefinabilityIteration SourceFiniteCutoffShift SourceDn
 SourceRepresentationClosureRecipe SourceRepresentationFalsityClosure
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition source_environment_carrier_zero:sf_form:=∀(source_def_empty →$0 ∈' $1).
Lemma environment_empty_cutoff :C.subst_form(source_shift_sigma 1)source_def_empty=source_def_empty.
Proof. reflexivity. Qed.
Theorem source_environment_carrier_zero_graph M:
 source_environment_carrier_recipe M(zeroM M)(code_numeral M(sf_encode source_environment_carrier_zero)).
Proof.
 exists(code_numeral M(sf_encode source_def_empty)),(code_numeral M(sf_encode source_def_empty)),
  (code_numeral M(sf_encode source_def_empty)),(code_numeral M(sf_encode source_environment_carrier_zero)).
 split;[apply source_def_iteration_zero;reflexivity|].
 assert(HS:source_cutoff_shift M 1(code_numeral M(sf_encode source_def_empty))(code_numeral M(sf_encode source_def_empty))).
 { rewrite <-environment_empty_cutoff at 2.
   exact(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)source_def_empty _ _(source_formula_numeral_graph M source_def_empty)(source_formula_numeral_graph M(C.subst_form(source_shift_sigma 1)source_def_empty))). }
 split;[exact HS|]. split;[exact HS|]. split.
 - unfold E_environment_carrier_point,source_environment_carrier_zero.
   eapply environment_carrier_code_join;[|reflexivity|exact(sf_make_numeral M SFAll _ 0)].
   eapply environment_carrier_code_join;[reflexivity| |exact(sf_make_numeral M SFImpl _ _)].
   exact(sf_make_numeral M SFMember 0 1).
 - apply source_dn_zero. reflexivity.
Qed.
Lemma source_environment_carrier_zero_shape:source_environment_carrier_zero_law=
 source_def_successor01 →representation_closure_condition →∃($0 ∈' $3 ∧source_environment_carrier_zero).
Proof. reflexivity. Qed.
Local Opaque source_def_successor01 representation_closure_condition source_environment_carrier_zero.
Theorem source_zfr_environment_carrier_zero M carrier out:
 source_environment_carrier_recipe M(zeroM M)carrier ->
 source_environment_carrier_closure_statement M carrier out ->source_zfr_provable M out.
Proof.
 intros HR HO. rewrite(source_environment_carrier_recipe_functional M(zeroM M)carrier
  (code_numeral M(sf_encode source_environment_carrier_zero))HR(source_environment_carrier_zero_graph M))in HO.
 set(p:=sf_encode source_environment_carrier_zero). set(m:=sf_make SFMember 0 3). set(b:=sf_make SFAnd m p).
 set(e:=sf_make SFEx b 0). set(c:=sf_encode representation_closure_condition). set(s:=sf_encode source_def_successor01).
 set(i:=sf_make SFImpl c e). set(o:=sf_make SFImpl s i).
 assert(HCanon:source_environment_carrier_closure_statement M(code_numeral M p)(code_numeral M o)).
 { apply(source_environment_carrier_closure_statement_join M(code_numeral M p)(code_numeral M b)(code_numeral M e)(code_numeral M i)(code_numeral M o)).
   - exact(sf_make_numeral M SFAnd m p).
   - exact(sf_make_numeral M SFEx b 0).
   - exact(sf_make_numeral M SFImpl c e).
   - exact(sf_make_numeral M SFImpl s i). }
 rewrite(source_environment_carrier_closure_statement_functional M _ out(code_numeral M o)HO HCanon).
 pose proof(finite_old_zfr_proof_lift M old_L_background old_environment_carrier_zero_law
  old_L_background_valid old_environment_carrier_zero_proof)as P.
 change(source_zfr_provable M(code_numeral M(sf_encode source_environment_carrier_zero_law)))in P.
 rewrite source_environment_carrier_zero_shape in P. exact P.
Qed.
Print Assumptions source_environment_carrier_zero_graph.
Print Assumptions source_zfr_environment_carrier_zero.
