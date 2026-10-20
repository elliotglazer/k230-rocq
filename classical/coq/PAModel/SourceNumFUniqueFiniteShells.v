(** Exact finite comparison shell and equality shifts in the NumF induction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceQuantifierRules SourceNumFComparisonFixed SourceNumFUniqueSyntax SourceNumFClosureFiniteShells
 SourceDefinabilityPrimitives OldNamedSyntaxBridge OldFullNDSourceBridge SourceZFRProvability.
From OldZFC Require Z_base.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Open Scope minZFsyn.
Unset Implicit Arguments.
Definition numf_equal_code M a b :=code_numeral M(sf_make SFEqual a b).
Theorem source_numf_equal_shift M a b :source_formula_shift M(numf_equal_code M a b)(numf_equal_code M(S a)(S b)).
Proof. exact(source_formula_numeral_shift M($a ≡' $b)). Qed.
Theorem source_numf_unique_square_shell M :exists tail middle law,
 sf_relation M SFImpl(code_numeral M(sf_encode numf_successor03))(numf_equal_code M 2 3)tail /\
 sf_relation M SFImpl(numf_closure_succ_shift_code M)tail middle /\
 sf_relation M SFImpl(numf_equal_code M 0 1)middle law /\source_zfr_provable M law.
Proof.
 set(e:=sf_make SFEqual 0 1). set(f:=sf_make SFEqual 2 3).
 set(a:=sf_encode numf_closure_succ_shift_form). set(b:=sf_encode numf_successor03).
 set(t:=sf_make SFImpl b f). set(m:=sf_make SFImpl a t). set(l:=sf_make SFImpl e m).
 exists(code_numeral M t),(code_numeral M m),(code_numeral M l).
 split;[exact(sf_make_numeral M SFImpl b f)|].
 split;[exact(sf_make_numeral M SFImpl a t)|].
 split;[exact(sf_make_numeral M SFImpl e m)|].
 pose proof(source_zfr_numf_successor_square_fixed M)as P. rewrite numf_successor_square_shape in P. exact P.
Qed.
Lemma numf_empty_shift_shape :source_def_empty[↑]=isolated_formula(OldZFC.Z_base.Emp0(@OC.var OB.sig_empty 1)).
Proof.
 unfold source_def_empty. pose proof(isolated_old_formula_shift(OldZFC.Z_base.Emp0(@OC.var OB.sig_empty 0)))as E.
 rewrite OldZFC.Z_base.Emp0_subst in E. exact(eq_sym E).
Qed.
Lemma numf_empty_unique_shape :source_numf_empty_unique_law=(source_def_empty →source_def_empty[↑] →$0 ≡' $1).
Proof. rewrite numf_empty_shift_shape. reflexivity. Qed.
Print Assumptions source_numf_equal_shift.
Print Assumptions source_numf_unique_square_shell.
