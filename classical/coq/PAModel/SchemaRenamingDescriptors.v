(** Concrete beta descriptors for the four body transformations in minZF.
    These small standard certificates are proved in every ordinary PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  NumericalRenamingMaps NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Inductive schema_renaming_kind := SepBody | RepA | RepB | RepC.
Definition schema_dividend s := match s with SepBody=>0 | RepA=>22 | RepB=>14 | RepC=>4 end.
Definition schema_modulus s := match s with SepBody=>0 | RepA|RepB=>3 | RepC=>1 end.
Definition schema_length s := match s with SepBody=>1 | _=>2 end.
Definition schema_delta s := match s with RepA|RepB=>1 | _=>2 end.
Definition schema_first s := match s with RepA|RepB=>2 | _=>0 end.
Definition schema_second s := match s with SepBody=>3 | RepA|RepC=>1 | RepB=>0 end.

Lemma descriptor_numeral_add M a b :
  addM M (code_numeral M a) (code_numeral M b)=code_numeral M (a+b).
Proof.
  induction a as [|a IH]; cbn [code_numeral Nat.add].
  - apply Arithmetic.add_zero.
  - rewrite Arithmetic.add_succ,IH. reflexivity.
Qed.
Lemma descriptor_numeral_mul M a b :
  mulM M (code_numeral M a) (code_numeral M b)=code_numeral M (a*b).
Proof.
  induction a as [|a IH]; cbn [code_numeral Nat.mul].
  - apply Arithmetic.mul_zero.
  - rewrite Arithmetic.mul_succ,IH,descriptor_numeral_add. reflexivity.
Qed.
Lemma descriptor_beta_certificate M b c i r q :
  r < S ((S i)*c) -> b=q*(S ((S i)*c))+r ->
  beta M (code_numeral M b) (code_numeral M c) (code_numeral M i) (code_numeral M r).
Proof.
  intros Hr Hb. unfold beta,beta_modulus.
  change (remainder M (code_numeral M b)
    (succM M (mulM M (code_numeral M (S i)) (code_numeral M c))) (code_numeral M r)).
  rewrite descriptor_numeral_mul. change (remainder M (code_numeral M b)
    (code_numeral M (S ((S i)*c))) (code_numeral M r)).
  split; [apply sf_numeral_lt;exact Hr|]. exists (code_numeral M q).
  rewrite descriptor_numeral_mul,descriptor_numeral_add,Hb. reflexivity.
Qed.

Lemma schema_beta_first M s :
  beta M (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (zeroM M) (code_numeral M (schema_first s)).
Proof.
  destruct s.
  - apply (descriptor_beta_certificate M 0 0 0 0 0); reflexivity || lia.
  - apply (descriptor_beta_certificate M 22 3 0 2 5); reflexivity || lia.
  - apply (descriptor_beta_certificate M 14 3 0 2 3); reflexivity || lia.
  - apply (descriptor_beta_certificate M 4 1 0 0 2); reflexivity || lia.
Qed.
Lemma schema_beta_second M s : s<>SepBody ->
  beta M (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
    (code_numeral M 1) (code_numeral M (schema_second s)).
Proof.
  intro H. destruct s; [contradiction| | |].
  - apply (descriptor_beta_certificate M 22 3 1 1 3); reflexivity || lia.
  - apply (descriptor_beta_certificate M 14 3 1 0 2); reflexivity || lia.
  - apply (descriptor_beta_certificate M 4 1 1 1 1); reflexivity || lia.
Qed.

Definition schema_lookup M s i v :=
  renaming_lookup M (code_numeral M (schema_dividend s))
    (code_numeral M (schema_modulus s)) (code_numeral M (schema_length s))
    (code_numeral M (schema_delta s)) i v.

Theorem schema_lookup_first M s v : schema_lookup M s (zeroM M) v <->
  v=code_numeral M (schema_first s).
Proof.
  unfold schema_lookup. rewrite renaming_lookup_inside.
  - split.
    + intro Hv. eapply beta_unique; [exact Hv|apply schema_beta_first].
    + intros ->. apply schema_beta_first.
  - destruct s; apply coding_zero_lt_succ.
Qed.
Theorem schema_lookup_second M s v : schema_lookup M s (code_numeral M 1) v <->
  v=code_numeral M (schema_second s).
Proof.
  destruct s.
  - unfold schema_lookup. rewrite renaming_lookup_outside.
    + change (v=addM M (code_numeral M 1) (code_numeral M 2) <-> v=code_numeral M 3).
      rewrite descriptor_numeral_add. reflexivity.
    + intro H. apply (proj1 (coding_lt_succ_cancel M (zeroM M) (zeroM M))) in H.
      exact (coding_not_lt_zero M (zeroM M) H).
  - unfold schema_lookup. rewrite renaming_lookup_inside; [|apply coding_lt_succ].
    split; [intro H; eapply beta_unique; [exact H|apply schema_beta_second;discriminate]|].
    intros ->. apply schema_beta_second. discriminate.
  - unfold schema_lookup. rewrite renaming_lookup_inside; [|apply coding_lt_succ].
    split; [intro H; eapply beta_unique; [exact H|apply schema_beta_second;discriminate]|].
    intros ->. apply schema_beta_second. discriminate.
  - unfold schema_lookup. rewrite renaming_lookup_inside; [|apply coding_lt_succ].
    split; [intro H; eapply beta_unique; [exact H|apply schema_beta_second;discriminate]|].
    intros ->. apply schema_beta_second. discriminate.
Qed.
Theorem schema_lookup_tail M s i v : ~coding_lt M i (code_numeral M (schema_length s)) ->
  (schema_lookup M s i v <-> v=addM M i (code_numeral M (schema_delta s))).
Proof. apply renaming_lookup_outside. Qed.

Definition schema_renaming M s f body := numerical_renaming M f
  (code_numeral M (schema_dividend s)) (code_numeral M (schema_modulus s))
  (code_numeral M (schema_length s)) (code_numeral M (schema_delta s)) body.
Definition schema_renaming_formula s (f body : pa_term) : pa_form :=
  numerical_renaming_formula f (num (schema_dividend s)) (num (schema_modulus s))
    (num (schema_length s)) (num (schema_delta s)) body.
Lemma schema_renaming_formula_correct M rho s f body :
  holds M rho (schema_renaming_formula s f body) <->
  schema_renaming M s (evalM M rho f) (evalM M rho body).
Proof.
  unfold schema_renaming_formula,schema_renaming.
  rewrite numerical_renaming_formula_correct. now rewrite !code_eval_num.
Qed.
Lemma schema_renaming_total M s f : exists body, schema_renaming M s f body.
Proof. apply numerical_renaming_total. Qed.
Lemma schema_renaming_functional M s f body body' :
  schema_renaming M s f body -> schema_renaming M s f body' -> body=body'.
Proof. apply numerical_renaming_functional. Qed.
