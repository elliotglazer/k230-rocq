(** Exact internally finite conjunction of unary source-predicate instances.
    This is syntax, with actual numerical instantiation at every table row. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula
  CodeExpressions NumericalProofs NumericalContexts NumericalEnvironments InternalRecursion
  ProofClosure SourceContextConjunction SourceContextConjunctionExtensional SetFormulaCodes NumericalInstantiation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_predicate_context M start domain n b c :=forall i f,
  coding_lt M i n ->beta M b c i f ->numerical_instantiation M domain (addM M i start) f.
Definition source_predicate_context_formula (start domain n b c:term):form :=
  ∀∀ (Peano.sless $1 n`[↑]`[↑] →beta_formula b`[↑]`[↑] c`[↑]`[↑] $1 $0 →
    numerical_instantiation_formula domain`[↑]`[↑] ($1 ⊕start`[↑]`[↑]) $0).
Lemma source_predicate_eval_add M rho t u :
  evalM M rho (t ⊕u)=addM M (evalM M rho t)(evalM M rho u).
Proof. reflexivity. Qed.
Local Opaque holds beta_formula numerical_instantiation_formula.
Lemma source_predicate_context_formula_correct M rho start domain n b c :
  holds M rho (source_predicate_context_formula start domain n b c) <->
  source_predicate_context M (evalM M rho start)(evalM M rho domain)(evalM M rho n)
    (evalM M rho b)(evalM M rho c).
Proof.
  unfold source_predicate_context_formula,source_predicate_context.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite holds_sless. setoid_rewrite beta_formula_correct.
  setoid_rewrite numerical_instantiation_formula_correct. setoid_rewrite source_predicate_eval_add.
  setoid_rewrite source_context_conjunction_eval_lift2. reflexivity.
Qed.

Definition source_predicate_context_step:form :=numerical_instantiation_formula $5 ($1 ⊕$4) $0.
Lemma source_predicate_context_step_correct M start domain b c i f :
  recursion_step M source_predicate_context_step (start .: domain .: fun _=>zeroM M) b c i f <->
  numerical_instantiation M domain (addM M i start) f.
Proof. unfold recursion_step,source_predicate_context_step. rewrite numerical_instantiation_formula_correct. reflexivity. Qed.

Theorem source_predicate_context_total M start domain n :exists b c,source_predicate_context M start domain n b c.
Proof.
  assert (HT:forall b c i,exists f,recursion_step M source_predicate_context_step
    (start .: domain .: fun _=>zeroM M) b c i f).
  { intros b c i. setoid_rewrite source_predicate_context_step_correct. apply numerical_instantiation_total. }
  assert (HP:forall b c b' c' i,prefix M b c b' c' i ->forall f,
    (recursion_step M source_predicate_context_step (start .: domain .: fun _=>zeroM M) b c i f <->
     recursion_step M source_predicate_context_step (start .: domain .: fun _=>zeroM M) b' c' i f)).
  { intros. rewrite !source_predicate_context_step_correct. reflexivity. }
  destruct (recursion_table_total M source_predicate_context_step
    (start .: domain .: fun _=>zeroM M) HT HP n) as [b [c HC]].
  exists b,c. intros i f HI HF.
  exact (proj1 (source_predicate_context_step_correct M start domain b c i f) (HC i f HI HF)).
Qed.

Lemma source_predicate_context_prefix M start domain n b c :
  source_predicate_context M start domain (succM M n) b c ->source_predicate_context M start domain n b c.
Proof. intros HC i f HI HF. exact (HC i f (coding_lt_trans M i n (succM M n) HI (coding_lt_succ M n)) HF). Qed.
Lemma source_predicate_context_same_rows M start domain n b c d e :
  source_predicate_context M start domain n b c ->source_predicate_context M start domain n d e ->
  source_context_same_rows M b c d e n.
Proof. intros HB HD i f g HI HF HG. exact (numerical_instantiation_functional M domain (addM M i start) f g
  (HB i f HI HF)(HD i g HI HG)). Qed.

Definition source_predicate_block M start domain n result :=exists b c,
  source_predicate_context M start domain n b c /\source_context_conjunction M b c n result.
Definition source_predicate_block_formula (start domain n result:term):form :=
  ∃∃ (source_predicate_context_formula start`[↑]`[↑] domain`[↑]`[↑] n`[↑]`[↑] $1 $0 ∧
    source_context_conjunction_formula $1 $0 n`[↑]`[↑] result`[↑]`[↑]).
Local Opaque source_predicate_context_formula source_context_conjunction_formula.
Lemma source_predicate_block_formula_correct M rho start domain n result :
  holds M rho (source_predicate_block_formula start domain n result) <->
  source_predicate_block M (evalM M rho start)(evalM M rho domain)(evalM M rho n)(evalM M rho result).
Proof.
  unfold source_predicate_block_formula,source_predicate_block.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_predicate_context_formula_correct.
  setoid_rewrite source_context_conjunction_formula_correct.
  setoid_rewrite source_context_conjunction_eval_lift2. reflexivity.
Qed.

Theorem source_predicate_block_total M start domain n :exists result,source_predicate_block M start domain n result.
Proof.
  destruct (source_predicate_context_total M start domain n) as [b [c HC]].
  destruct (source_context_conjunction_total M b c n) as [result HR]. exists result,b,c. auto.
Qed.
Theorem source_predicate_block_functional M start domain n f g :
  source_predicate_block M start domain n f ->source_predicate_block M start domain n g ->f=g.
Proof.
  intros [b [c [HC HF]]] [d [e [HD HG]]].
  exact (source_context_conjunction_extensional M b c d e n f g HF HG
    (source_predicate_context_same_rows M start domain n b c d e HC HD)).
Qed.
Theorem source_predicate_block_zero M start domain result :
  source_predicate_block M start domain (zeroM M) result <->sf_relation M SFImpl (zeroM M)(zeroM M) result.
Proof.
  split;[intros [b [c [_ HF]]];apply source_context_conjunction_zero in HF;exact HF|intro HF].
  destruct (source_predicate_context_total M start domain (zeroM M)) as [b [c HC]].
  exists b,c. split;[exact HC|apply source_context_conjunction_zero;exact HF].
Qed.
Theorem source_predicate_block_succ M start domain n result :
  source_predicate_block M start domain (succM M n) result <->exists p h,
    source_predicate_block M start domain n p /\numerical_instantiation M domain (addM M n start) h /\sf_relation M SFAnd p h result.
Proof.
  assert (Forward:forall f,source_predicate_block M start domain (succM M n) f ->exists p h,
    source_predicate_block M start domain n p /\numerical_instantiation M domain (addM M n start) h /\sf_relation M SFAnd p h f).
  { intros f [b [c [HC HF]]]. apply source_context_conjunction_succ in HF.
    destruct HF as [p [h [HP [HH HAnd]]]]. exists p,h. split.
    - exists b,c. split;[exact (source_predicate_context_prefix M start domain n b c HC)|exact HP].
    - split;[exact (HC n h (coding_lt_succ M n) HH)|exact HAnd]. }
  split;[apply Forward|]. intros [p [h [HP [HH HAnd]]]].
  destruct (source_predicate_block_total M start domain (succM M n)) as [f HF].
  destruct (Forward f HF) as [q [j [HQ [HJ HAnd']]]].
  pose proof (source_predicate_block_functional M start domain n p q HP HQ) as E. subst q.
  pose proof (numerical_instantiation_functional M domain (addM M n start) h j HH HJ) as E. subst j.
  pose proof (sf_relation_functional M SFAnd p h f result HAnd' HAnd) as E. now subst f.
Qed.

Print Assumptions source_predicate_context_formula_correct.
Print Assumptions source_predicate_context_total.
Print Assumptions source_predicate_block_formula_correct.
Print Assumptions source_predicate_block_total.
Print Assumptions source_predicate_block_functional.
Print Assumptions source_predicate_block_zero.
Print Assumptions source_predicate_block_succ.
