(** Exact-length numerical sequents for the full source formula syntax.
    Ordinary rows and auxiliary DE-branch rows are disjoint tagged records. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeTuples CodeExpressions
  NumericalProofs NumericalContexts SourceBounded SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_sequent M b c n f r :=
  tuple7_graph M (zeroM M) b c n f (zeroM M) (zeroM M) r.
Definition source_branches M b c n a d f r :=
  tuple7_graph M (succM M (zeroM M)) b c n a d f r.

Definition source_sequent_formula (b c n f r : term) : form :=
  tuple7_formula zero b c n f zero zero r.
Definition source_branches_formula (b c n a d f r : term) : form :=
  tuple7_formula (σ zero) b c n a d f r.

Theorem source_sequent_formula_correct M rho b c n f r :
  holds M rho (source_sequent_formula b c n f r) <->
  source_sequent M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho f) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.

Theorem source_branches_formula_correct M rho b c n a d f r :
  holds M rho (source_branches_formula b c n a d f r) <->
  source_branches M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho a) (evalM M rho d) (evalM M rho f) (evalM M rho r).
Proof. apply tuple7_formula_correct. Qed.

Theorem source_sequent_total M b c n f : exists r, source_sequent M b c n f r.
Proof. apply tuple7_total. Qed.
Theorem source_branches_total M b c n a d f : exists r, source_branches M b c n a d f r.
Proof. apply tuple7_total. Qed.

Theorem source_sequent_injective M b c n f b' c' n' f' r :
  source_sequent M b c n f r -> source_sequent M b' c' n' f' r ->
  b=b' /\ c=c' /\ n=n' /\ f=f'.
Proof.
  intros H H'. pose proof (tuple7_injective M _ _ _ _ _ _ _ _ _ _ _ _ _ _ r H H'). tauto.
Qed.

Theorem source_branches_injective M b c n a d f b' c' n' a' d' f' r :
  source_branches M b c n a d f r -> source_branches M b' c' n' a' d' f' r ->
  b=b' /\ c=c' /\ n=n' /\ a=a' /\ d=d' /\ f=f'.
Proof.
  intros H H'. pose proof (tuple7_injective M _ _ _ _ _ _ _ _ _ _ _ _ _ _ r H H'). tauto.
Qed.

Theorem source_row_kinds_disjoint M b c n f b' c' n' a d f' r :
  source_sequent M b c n f r -> ~source_branches M b' c' n' a d f' r.
Proof.
  intros H H'. pose proof (tuple7_injective M _ _ _ _ _ _ _ _ _ _ _ _ _ _ r H H') as [E _].
  pose proof (coding_zero_lt_succ M (zeroM M)) as Hlt.
  rewrite <- E in Hlt. exact (coding_not_lt_zero M (zeroM M) Hlt).
Qed.

Theorem source_sequent_formula_bound : bounded 5 (source_sequent_formula $0 $1 $2 $3 $4).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
Theorem source_branches_formula_bound : bounded 7 (source_branches_formula $0 $1 $2 $3 $4 $5 $6).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Definition source_sequent_wf M b c n f := exists k,
  source_bounded M f k /\ context_bounded M b c n k.
Definition source_branches_wf M b c n a d f := exists k,
  source_bounded M a k /\ source_bounded M d k /\ source_bounded M f k /\ context_bounded M b c n k.

Definition source_sequent_wf_formula (b c n f : term) : form :=
  ∃ (source_bounded_accept_formula (context_lift f) $0 ∧
    context_bounded_formula (context_lift b) (context_lift c) (context_lift n) $0).
Definition source_branches_wf_formula (b c n a d f : term) : form :=
  ∃ (source_bounded_accept_formula (context_lift a) $0 ∧
    (source_bounded_accept_formula (context_lift d) $0 ∧
    (source_bounded_accept_formula (context_lift f) $0 ∧
    context_bounded_formula (context_lift b) (context_lift c) (context_lift n) $0))).

Local Opaque holds source_bounded_accept_formula context_bounded_formula source_sequent_formula source_branches_formula.
Theorem source_sequent_wf_formula_correct M rho b c n f :
  holds M rho (source_sequent_wf_formula b c n f) <->
  source_sequent_wf M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold source_sequent_wf_formula,source_sequent_wf.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite context_eval_lift. reflexivity.
Qed.
Theorem source_branches_wf_formula_correct M rho b c n a d f :
  holds M rho (source_branches_wf_formula b c n a d f) <->
  source_branches_wf M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho a) (evalM M rho d) (evalM M rho f).
Proof.
  unfold source_branches_wf_formula,source_branches_wf.
  setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite context_eval_lift. reflexivity.
Qed.

Definition source_row_wf M r :=
  (exists b c n f, source_sequent M b c n f r /\ source_sequent_wf M b c n f) \/
  (exists b c n a d f, source_branches M b c n a d f r /\ source_branches_wf M b c n a d f).
Definition source_row_wf_formula (r : term) : form :=
  (∃∃∃∃ (source_sequent_formula $3 $2 $1 $0 r`[↑]`[↑]`[↑]`[↑] ∧
    source_sequent_wf_formula $3 $2 $1 $0)) ∨
  (∃∃∃∃∃∃ (source_branches_formula $5 $4 $3 $2 $1 $0 r`[↑]`[↑]`[↑]`[↑]`[↑]`[↑] ∧
    source_branches_wf_formula $5 $4 $3 $2 $1 $0)).

Local Opaque source_sequent_wf_formula source_branches_wf_formula.
Theorem source_row_wf_formula_correct M rho r :
  holds M rho (source_row_wf_formula r) <-> source_row_wf M (evalM M rho r).
Proof.
  unfold source_row_wf_formula,source_row_wf.
  setoid_rewrite holds_or. repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite source_branches_formula_correct.
  setoid_rewrite source_sequent_wf_formula_correct. setoid_rewrite source_branches_wf_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_sequent_wf_from_row M b c n f r :
  source_sequent M b c n f r -> source_row_wf M r -> source_sequent_wf M b c n f.
Proof.
  intros H [[b' [c' [n' [f' [H' Hw]]]]]|[b' [c' [n' [a [d [f' [H' Hw]]]]]]]].
  - destruct (source_sequent_injective M _ _ _ _ _ _ _ _ r H H') as [-> [-> [-> ->]]]. exact Hw.
  - exfalso. exact (source_row_kinds_disjoint M _ _ _ _ _ _ _ _ _ _ r H H').
Qed.

Theorem source_branches_wf_from_row M b c n a d f r :
  source_branches M b c n a d f r -> source_row_wf M r -> source_branches_wf M b c n a d f.
Proof.
  intros H [[b' [c' [n' [f' [H' Hw]]]]]|[b' [c' [n' [a' [d' [f' [H' Hw]]]]]]]].
  - exfalso. exact (source_row_kinds_disjoint M _ _ _ _ _ _ _ _ _ _ r H' H).
  - destruct (source_branches_injective M _ _ _ _ _ _ _ _ _ _ _ _ r H H')
      as [-> [-> [-> [-> [-> ->]]]]]. exact Hw.
Qed.



