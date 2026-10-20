(** Actual NumF-in-C proof production at every index of an arbitrary PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes
 SourceNumeralLift SourceDefinabilityPrimitives SourceDefinabilityBounds SourceDefinabilityIteration
 SourceRepresentationClosureRecipe SourceNumFClosureRecipe SourceNumFClosureStep SourceNumFClosureSyntax SourceClosureNumeralsOld SourceClosureNumeralsFixed
 SourceLFixed SourceLNonempty OldNamedSyntaxBridge OldZFRProofLift SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Lemma source_numf_closure_empty_shape :source_closure_empty_law=
 (source_def_successor01 →representation_closure_condition →∃(source_def_empty ∧$0 ∈' $3)).
Proof. reflexivity. Qed.
Local Opaque source_def_successor01 representation_closure_condition source_def_empty.
Theorem source_zfr_numf_closure_zero M out :
 source_numf_closure_statement M(code_numeral M(sf_encode source_def_empty))out ->source_zfr_provable M out.
Proof.
 intro H.
 set(p:=sf_encode source_def_empty). set(m:=sf_make SFMember 0 3). set(b:=sf_make SFAnd p m).
 set(e:=sf_make SFEx b 0). set(c:=sf_encode representation_closure_condition). set(s:=sf_encode source_def_successor01).
 set(i:=sf_make SFImpl c e). set(o:=sf_make SFImpl s i).
 assert(HCanon:source_numf_closure_statement M(code_numeral M p)(code_numeral M o)).
 { apply(source_numf_closure_statement_join M(code_numeral M p)(code_numeral M b)(code_numeral M e)(code_numeral M i)(code_numeral M o)).
   - split;[exact(sf_make_numeral M SFAnd p m)|exact(sf_make_numeral M SFEx b 0)].
   - exact(sf_make_numeral M SFImpl c e).
   - exact(sf_make_numeral M SFImpl s i). }
 rewrite(source_numf_closure_statement_functional M _ out(code_numeral M o)H HCanon).
 pose proof(finite_old_zfr_proof_lift M old_L_background old_closure_empty_law old_L_background_valid old_closure_empty_proof)as P.
 change(source_zfr_provable M(code_numeral M(sf_encode source_closure_empty_law)))in P.
 rewrite source_numf_closure_empty_shape in P. exact P.
Qed.
Definition source_numf_closure_proof_at M n :=forall matrix out,
 source_numf M n matrix ->source_numf_closure_statement M matrix out ->source_zfr_provable M out.
Definition source_numf_closure_proof_formula :form :=∀∀(
 source_numf_formula $2 $1 →source_numf_closure_statement_formula $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds source_numf_formula source_numf_closure_statement_formula source_zfr_provable_formula.
Theorem source_numf_closure_proof_definable M :Definable1 M(source_numf_closure_proof_at M).
Proof.
 exists source_numf_closure_proof_formula,(fun _=>zeroM M). intro n.
 unfold source_numf_closure_proof_formula,source_numf_closure_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all. repeat setoid_rewrite NumericalProofs.holds_imp.
 setoid_rewrite source_numf_formula_correct. setoid_rewrite source_numf_closure_statement_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Theorem source_zfr_numf_closure_uniform M :forall n,source_numf_closure_proof_at M n.
Proof.
 apply(definable_induction M(source_numf_closure_proof_at M)(source_numf_closure_proof_definable M)).
 - intros matrix out HM HO. apply source_def_iteration_zero in HM. subst matrix. exact(source_zfr_numf_closure_zero M out HO).
 - intros n IH matrix out HM HO. apply source_def_iteration_succ in HM. destruct HM as(previous&HP&HStep).
   destruct(source_numf_closure_statement_total M previous)as(old&HOld).
   exact(source_zfr_numf_closure_step M previous matrix old out(source_numf_bound M n previous HP)HStep HOld HO(IH previous old HP HOld)).
Qed.
Theorem source_zfr_numf_closure_total M n :exists matrix out,
 source_numf M n matrix /\source_numf_closure_statement M matrix out /\source_zfr_provable M out.
Proof.
 destruct(source_numf_total M n)as(matrix&HM).
 destruct(source_numf_closure_statement_total M matrix)as(out&HO).
 exists matrix,out. exact(conj HM(conj HO(source_zfr_numf_closure_uniform M n matrix out HM HO))).
Qed.
Print Assumptions source_zfr_numf_closure_zero.
Print Assumptions source_numf_closure_proof_definable.
Print Assumptions source_zfr_numf_closure_uniform.
Print Assumptions source_zfr_numf_closure_total.
