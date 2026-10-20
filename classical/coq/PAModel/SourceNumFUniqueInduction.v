(** Uniform actual uniqueness proofs for every internally indexed NumF. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SourceNumeralLift
 SourceBounded SourceDefinabilityPrimitives SourceDefinabilityBounds SourceDefinabilityIteration
 SourceNumFUniqueRecipe SourceNumFUniqueStep SourceNumFUniqueFiniteShells SourceNumFComparisonFixed SourceZFRProvability.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Local Opaque source_def_empty.
Theorem source_zfr_numf_unique_zero M out :source_numf_unique_recipe M(code_numeral M(sf_encode source_def_empty))out ->source_zfr_provable M out.
Proof.
 intro H. set(p:=sf_encode source_def_empty). set(ps:=sf_encode source_def_empty[↑]).
 set(e:=sf_make SFEqual 0 1). set(i:=sf_make SFImpl ps e). set(o:=sf_make SFImpl p i).
 assert(HCanon:source_numf_unique_recipe M(code_numeral M p)(code_numeral M o)).
 { apply(source_numf_unique_recipe_join M(code_numeral M p)(code_numeral M ps)(code_numeral M i)(code_numeral M o)).
   - exact(source_formula_numeral_shift M source_def_empty).
   - exact(sf_make_numeral M SFImpl ps e).
   - exact(sf_make_numeral M SFImpl p i). }
 rewrite(source_numf_unique_recipe_functional M _ out(code_numeral M o)H HCanon).
 pose proof(source_zfr_numf_empty_unique_fixed M)as P. rewrite numf_empty_unique_shape in P. exact P.
Qed.
Definition source_numf_unique_proof_at M n :=forall matrix out,
 source_numf M n matrix ->source_numf_unique_recipe M matrix out ->source_zfr_provable M out.
Definition source_numf_unique_proof_formula :form :=∀∀(
 source_numf_formula $2 $1 →source_numf_unique_recipe_formula $1 $0 →source_zfr_provable_formula $0).
Local Opaque holds source_numf_formula source_numf_unique_recipe_formula source_zfr_provable_formula.
Theorem source_numf_unique_proof_definable M :Definable1 M(source_numf_unique_proof_at M).
Proof.
 exists source_numf_unique_proof_formula,(fun _=>zeroM M). intro n.
 unfold source_numf_unique_proof_formula,source_numf_unique_proof_at.
 repeat setoid_rewrite NumericalProofs.holds_all. repeat setoid_rewrite NumericalProofs.holds_imp.
 setoid_rewrite source_numf_formula_correct. setoid_rewrite source_numf_unique_recipe_formula_correct.
 setoid_rewrite source_zfr_provable_formula_correct. reflexivity.
Qed.
Theorem source_zfr_numf_unique_uniform M :forall n,source_numf_unique_proof_at M n.
Proof.
 apply(definable_induction M(source_numf_unique_proof_at M)(source_numf_unique_proof_definable M)).
 - intros matrix out HM HO. apply source_def_iteration_zero in HM. subst matrix. exact(source_zfr_numf_unique_zero M out HO).
 - intros n IH matrix out HM HO. apply source_def_iteration_succ in HM. destruct HM as(previous&HP&HStep).
   destruct(source_numf_unique_recipe_total M previous)as(old&HOld).
   exact(source_zfr_numf_unique_step M previous matrix old out(source_numf_bound M n previous HP)HStep HOld HO(IH previous old HP HOld)).
Qed.
Theorem source_zfr_numf_unique_total M n :exists matrix out,
 source_numf M n matrix /\source_numf_unique_recipe M matrix out /\source_zfr_provable M out.
Proof.
 destruct(source_numf_total M n)as(matrix&HM). destruct(source_numf_unique_recipe_total M matrix)as(out&HO).
 exists matrix,out. exact(conj HM(conj HO(source_zfr_numf_unique_uniform M n matrix out HM HO))).
Qed.
Print Assumptions source_zfr_numf_unique_zero.
Print Assumptions source_numf_unique_proof_definable.
Print Assumptions source_zfr_numf_unique_uniform.
Print Assumptions source_zfr_numf_unique_total.
