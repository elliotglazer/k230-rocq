(** Arithmetic presentation of exact-length context union, together with
    its compatibility with renaming and movement of one leading hypothesis. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
  NumericalContexts NumericalEnvironments NumericalContextRenaming
  ContextCombination SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition context_union_formula (b c n d e m u v l : term) : form :=
  (l == (n ⊕ m)) ∧ ∀
    ((context_member_formula (u`[↑]) (v`[↑]) (l`[↑]) $0 →
       (context_member_formula (b`[↑]) (c`[↑]) (n`[↑]) $0 ∨
        context_member_formula (d`[↑]) (e`[↑]) (m`[↑]) $0)) ∧
     ((context_member_formula (b`[↑]) (c`[↑]) (n`[↑]) $0 ∨
       context_member_formula (d`[↑]) (e`[↑]) (m`[↑]) $0) →
       context_member_formula (u`[↑]) (v`[↑]) (l`[↑]) $0)).

Local Transparent holds.
Lemma context_union_holds_eq M rho (a b : term) :
  holds M rho (a == b) <-> evalM M rho a = evalM M rho b.
Proof. reflexivity. Qed.
Lemma context_union_eval_add M rho (a b : term) :
  evalM M rho (a ⊕ b) = addM M (evalM M rho a) (evalM M rho b).
Proof. reflexivity. Qed.
Lemma context_union_eval_up M rho x (a : term) :
  evalM M (x .: rho) a`[↑] = evalM M rho a.
Proof. unfold evalM. apply eval_up. Qed.
Local Opaque holds context_member_formula.
Theorem context_union_formula_correct M rho b c n d e m u v l :
  holds M rho (context_union_formula b c n d e m u v l) <->
  context_union M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho d) (evalM M rho e) (evalM M rho m)
    (evalM M rho u) (evalM M rho v) (evalM M rho l).
Proof.
  unfold context_union_formula,context_union.
  repeat setoid_rewrite holds_and. setoid_rewrite holds_all.
  repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_imp.
  repeat setoid_rewrite holds_or. setoid_rewrite context_member_formula_correct.
  setoid_rewrite context_union_holds_eq.
  setoid_rewrite context_union_eval_add.
  setoid_rewrite context_union_eval_up. reflexivity.
Qed.

Theorem context_union_renaming M b c n d e m u v l
    p q k delta b' c' d' e' u' v' :
  context_union M b c n d e m u v l ->
  context_renaming M b c n p q k delta b' c' ->
  context_renaming M d e m p q k delta d' e' ->
  context_renaming M u v l p q k delta u' v' ->
  context_union M b' c' n d' e' m u' v' l.
Proof.
  intros [EL HU] HB HD HUV. split;[exact EL|]. intro g.
  rewrite (context_renaming_member_iff M u v l p q k delta u' v' g HUV).
  rewrite (context_renaming_member_iff M b c n p q k delta b' c' g HB).
  rewrite (context_renaming_member_iff M d e m p q k delta d' e' g HD).
  split.
  - intros [f [HF HG]]. apply HU in HF. destruct HF as [HF|HF].
    + left. exists f. auto.
    + right. exists f. auto.
  - intros [[f [HF HG]]|[f [HF HG]]];exists f;split;try exact HG;
      apply HU;[now left|now right].
Qed.

Theorem context_union_cons_right M b c n d e m u v l h d' e' m' u' v' l' :
  context_union M b c n d e m u v l ->
  environment_cons M d e m h d' e' m' ->
  environment_cons M u v l h u' v' l' ->
  context_union M b c n d' e' m' u' v' l'.
Proof.
  intros [EL HU] HD HUV. split.
  - rewrite (proj1 HD),(proj1 HUV),EL.
    rewrite (Arithmetic.add_comm M n (succM M m)),Arithmetic.add_succ.
    rewrite (Arithmetic.add_comm M m n). reflexivity.
  - intro f. rewrite (context_member_cons M u v l h u' v' l' f HUV).
    rewrite (context_member_cons M d e m h d' e' m' f HD).
    rewrite HU. tauto.
Qed.

Theorem context_union_formula_bound :
  bounded 9 (context_union_formula $0 $1 $2 $3 $4 $5 $6 $7 $8).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Print Assumptions context_union_formula_correct.
Print Assumptions context_union_renaming.
Print Assumptions context_union_cons_right.


