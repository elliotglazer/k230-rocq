(** Two-role abstraction used by KDecodeAbstract. Output role b has
    precedence, input a maps to1, and every remaining parameter i maps
    to i+2. The prefix length and matrices are arbitrary PA-model values. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking
  CodeExpressions NumericalProofs NumericalEnvironments NumericalRenamingMaps NumericalRenaming
  SetFormulaCodes SourceBounded SourceRenamingBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_role_length M a b :=succM M (addM M a b).
Definition source_role_index M a b i v :=
  (i  =  b /\v  =  zeroM M) \/(i<>b /\((i  =  a /\v  =  code_numeral M 1) \/
    (i<>a /\v  =  succM M (succM M i)))).
Definition source_role_index_formula (a b i v:term) :form :=
  ((i == b)∧(v == zero))∨((i == b→⊥)∧(((i == a)∧(v == num 1))∨((i == a→⊥)∧(v == σ(σ i))))).
Lemma source_role_index_formula_correct M rho a b i v :
  holds M rho (source_role_index_formula a b i v) <->
    source_role_index M (evalM M rho a) (evalM M rho b) (evalM M rho i) (evalM M rho v).
Proof. reflexivity. Qed.

Lemma source_role_eval_succ M rho t :evalM M rho (σ t) = succM M (evalM M rho t).
Proof. reflexivity. Qed.
Lemma source_role_eval_add M rho t u :evalM M rho (t⊕u) = addM M (evalM M rho t) (evalM M rho u).
Proof. reflexivity. Qed.

Definition source_role_map M a b rb rc :=forall i v,
  renaming_lookup M rb rc (source_role_length M a b) (code_numeral M 2) i v <->
    source_role_index M a b i v.
Definition source_role_map_formula (a b rb rc:term) :form :=
  ∀∀((renaming_lookup_formula (code_lift2 rb) (code_lift2 rc)
      (σ(code_lift2 a⊕code_lift2 b)) (num 2) $1 $0 →
      source_role_index_formula (code_lift2 a) (code_lift2 b) $1 $0)∧
    (source_role_index_formula (code_lift2 a) (code_lift2 b) $1 $0 →
      renaming_lookup_formula (code_lift2 rb) (code_lift2 rc)
        (σ(code_lift2 a⊕code_lift2 b)) (num 2) $1 $0)).

Lemma source_role_map_formula_correct M rho a b rb rc :
  holds M rho (source_role_map_formula a b rb rc) <->
    source_role_map M (evalM M rho a) (evalM M rho b) (evalM M rho rb) (evalM M rho rc).
Proof.
  set (body:=
    (renaming_lookup_formula (code_lift2 rb) (code_lift2 rc)
      (σ(code_lift2 a⊕code_lift2 b)) (num 2) $1 $0 →
      source_role_index_formula (code_lift2 a) (code_lift2 b) $1 $0)∧
    (source_role_index_formula (code_lift2 a) (code_lift2 b) $1 $0 →
      renaming_lookup_formula (code_lift2 rb) (code_lift2 rc)
        (σ(code_lift2 a⊕code_lift2 b)) (num 2) $1 $0)).
  change ((forall i v,holds M (v .: i .: rho) body) <->
    forall i v,renaming_lookup M (evalM M rho rb) (evalM M rho rc)
      (source_role_length M (evalM M rho a) (evalM M rho b)) (code_numeral M 2) i v <->
      source_role_index M (evalM M rho a) (evalM M rho b) i v).
  assert (HBody:forall i v,holds M (v .: i .: rho) body <->
    (renaming_lookup M (evalM M rho rb) (evalM M rho rc)
      (source_role_length M (evalM M rho a) (evalM M rho b)) (code_numeral M 2) i v <->
      source_role_index M (evalM M rho a) (evalM M rho b) i v)).
  { intros i v. unfold body. rewrite holds_and,!holds_imp,
      !renaming_lookup_formula_correct,!source_role_index_formula_correct.
    rewrite !source_role_eval_succ,!source_role_eval_add,!code_eval_num,!code_eval_lift2. reflexivity. }
  split;intros H i v;apply HBody,H.
Qed.

Lemma source_role_index_total M a b i :exists v,source_role_index M a b i v.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i b) as [E|NE].
  - exists (zeroM M). left;auto.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i a) as [E|NE'].
    + exists (code_numeral M 1). right;auto.
    + exists (succM M (succM M i)). right;auto.
Qed.
Lemma source_role_index_functional M a b i v w :
  source_role_index M a b i v ->source_role_index M a b i w ->v  =  w.
Proof. unfold source_role_index. intros [[H E]|[NE [[H E]|[NA E]]]] [[H' E']|[NE' [[H' E']|[NA' E']]]];congruence. Qed.

Lemma source_role_add_two M i :addM M i (code_numeral M 2) = succM M (succM M i).
Proof.
  rewrite Arithmetic.add_comm. change (addM M (succM M (succM M (zeroM M))) i = succM M (succM M i)).
  now rewrite !Arithmetic.add_succ,Arithmetic.add_zero.
Qed.

Theorem source_role_map_total M a b :exists rb rc,source_role_map M a b rb rc.
Proof.
  set (n:=source_role_length M a b).
  set (rho:=a .: b .: fun _=>zeroM M).
  set (F:=source_role_index_formula $2 $3 $1 $0).
  assert (HT:forall i,coding_lt M i n ->exists v,holds M (v .: i .: rho) F).
  { intros i _. exact (source_role_index_total M a b i). }
  assert (HB:forall i v,coding_lt M i n ->holds M (v .: i .: rho) F ->
      coding_lt M v (succM M (succM M n))).
  { intros i v HI [[_ ->]|[_ [[_ ->]|[_ ->]]]].
    - apply coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_zero_lt_succ.
    - apply coding_lt_succ_cancel,coding_lt_succ_cancel,HI. }
  assert (HU:forall i v w,coding_lt M i n ->holds M (v .: i .: rho) F ->
      holds M (w .: i .: rho) F ->v  =  w).
  { intros i v w _ HV HW. exact (source_role_index_functional M a b i v w HV HW). }
  destruct (beta_pack_function M rho F n (succM M n) HT HB HU) as (rb&rc&HBC).
  assert (HA:coding_lt M a n) by (unfold n,source_role_length;apply coding_le_add).
  assert (HBB:coding_lt M b n).
  { unfold n,source_role_length. rewrite (Arithmetic.add_comm M a b). apply coding_le_add. }
  exists rb,rc. intros i v. split.
  - intros [[HI HV]|[HI HV]].
    + exact (proj1 (HBC i v HI) HV).
    + right. split;[intro E;subst i;contradiction|]. right. split;[intro E;subst i;contradiction|].
      rewrite source_role_add_two in HV. exact HV.
  - intro H. destruct (environment_lt_cases M i n) as [HI|HI].
    + left. split;[exact HI|exact (proj2 (HBC i v HI) H)].
    + right. split;[exact HI|]. destruct H as [[E _]|[NE [[E _]|[_ ->]]]].
      * subst i. contradiction.
      * subst i. contradiction.
      * symmetry. apply source_role_add_two.
Qed.

Theorem source_role_map_bounds M a b rb rc k :source_role_map M a b rb rc ->
  renaming_maps_bound M rb rc (source_role_length M a b) (code_numeral M 2) k (succM M (succM M k)).
Proof.
  intros HM i v HI HV. apply (proj1 (HM i v)) in HV.
  destruct HV as [[_ ->]|[_ [[_ ->]|[_ ->]]]].
  - apply coding_zero_lt_succ.
  - apply coding_lt_succ_cancel,coding_zero_lt_succ.
  - apply coding_lt_succ_cancel,coding_lt_succ_cancel,HI.
Qed.

Definition source_role_abstraction M a b phi out :=exists rb rc,
  source_role_map M a b rb rc /\
  numerical_renaming M phi rb rc (source_role_length M a b) (code_numeral M 2) out.
Definition source_role_abstraction_formula (a b phi out:term) :form :=
  ∃∃(source_role_map_formula (code_lift2 a) (code_lift2 b) $1 $0 ∧
    numerical_renaming_formula (code_lift2 phi) $1 $0
      (σ(code_lift2 a⊕code_lift2 b)) (num 2) (code_lift2 out)).
Lemma source_role_abstraction_formula_correct M rho a b phi out :
  holds M rho (source_role_abstraction_formula a b phi out) <->
    source_role_abstraction M (evalM M rho a) (evalM M rho b) (evalM M rho phi) (evalM M rho out).
Proof.
  unfold source_role_abstraction_formula,source_role_abstraction,source_role_length.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_role_map_formula_correct. setoid_rewrite numerical_renaming_formula_correct.
  repeat setoid_rewrite source_role_eval_succ. repeat setoid_rewrite source_role_eval_add.
  repeat setoid_rewrite code_eval_num. repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.

Theorem source_role_abstraction_total M a b phi :exists out,source_role_abstraction M a b phi out.
Proof.
  destruct (source_role_map_total M a b) as (rb&rc&HM).
  destruct (numerical_renaming_total M phi rb rc (source_role_length M a b) (code_numeral M 2)) as (out&HO).
  exists out,rb,rc. auto.
Qed.

Theorem source_role_abstraction_bounded M a b phi out k :
  source_bounded M phi k ->source_role_abstraction M a b phi out ->
  source_bounded M out (succM M (succM M k)).
Proof.
  intros HB (rb&rc&HM&HR).
  exact (numerical_renaming_preserves_bound M phi rb rc (source_role_length M a b) (code_numeral M 2)
    out k (succM M (succM M k)) HB HR (source_role_map_bounds M a b rb rc k HM)).
Qed.

Print Assumptions source_role_map_total.
Print Assumptions source_role_abstraction_formula_correct.
Print Assumptions source_role_abstraction_bounded.
