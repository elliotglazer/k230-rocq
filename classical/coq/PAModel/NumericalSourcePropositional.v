(** Internally finite propositional source derivations. No translation or
    preservation hypothesis appears in the proof predicate or its rules. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs NumericalContexts NumericalEnvironments SourceSequents SourcePropositionalRules
  SetFormulaCodes SourceBounded NumericalTraces SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_prop_row M r := trace_derives M source_propositional_rules r.
Definition source_prop_prv M b c n f := exists r,
  source_sequent M b c n f r /\ source_prop_row M r.
Definition source_prop_branches M b c n a d f := exists r,
  source_branches M b c n a d f r /\ source_prop_row M r.

Definition source_prop_prv_formula (b c n f : term) : form :=
  ∃ (source_sequent_formula (context_lift b) (context_lift c) (context_lift n)
    (context_lift f) $0 ∧ trace_derives_formula source_propositional_rules $0).

Definition source_prop_branches_formula (b c n a d f : term) : form :=
  ∃ (source_branches_formula (context_lift b) (context_lift c) (context_lift n)
    (context_lift a) (context_lift d) (context_lift f) $0 ∧
    trace_derives_formula source_propositional_rules $0).

Local Opaque holds source_sequent_formula source_branches_formula trace_derives_formula source_row_wf_formula.
Theorem source_prop_prv_formula_correct M rho b c n f :
  holds M rho (source_prop_prv_formula b c n f) <->
  source_prop_prv M (evalM M rho b) (evalM M rho c) (evalM M rho n) (evalM M rho f).
Proof.
  unfold source_prop_prv_formula,source_prop_prv,source_prop_row.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_sequent_formula_correct. setoid_rewrite trace_derives_formula_correct.
  setoid_rewrite context_eval_lift. reflexivity.
Qed.
Theorem source_prop_prv_formula_bound : bounded 4 (source_prop_prv_formula $0 $1 $2 $3).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem source_prop_branches_formula_correct M rho b c n a d f :
  holds M rho (source_prop_branches_formula b c n a d f) <->
  source_prop_branches M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (evalM M rho a) (evalM M rho d) (evalM M rho f).
Proof.
  unfold source_prop_branches_formula,source_prop_branches,source_prop_row.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite source_branches_formula_correct. setoid_rewrite trace_derives_formula_correct.
  setoid_rewrite context_eval_lift. reflexivity.
Qed.
Theorem source_prop_branches_formula_bound : bounded 6 (source_prop_branches_formula $0 $1 $2 $3 $4 $5).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem source_prop_row_induction M (P : carrier M -> Prop) :
  Definable1 M P ->
  (forall r, source_prop_base M r -> P r) ->
  (forall r p, P p -> source_prop_unary M r p -> P r) ->
  (forall r p q, P p -> P q -> source_prop_binary M r p q -> P r) ->
  forall r, source_prop_row M r -> P r.
Proof.
  intros Hdef Hb Hu Hbin. apply (trace_derives_induction M source_propositional_rules P Hdef).
  - intros r H. apply Hb. now apply source_prop_trace_base in H.
  - intros r p Hp H. apply (Hu r p Hp). now apply source_prop_trace_unary in H.
  - intros r p q Hp Hq H. apply (Hbin r p q Hp Hq). now apply source_prop_trace_binary in H.
Qed.

Theorem source_prop_row_wellformed M r : source_prop_row M r -> source_row_wf M r.
Proof.
  apply (source_prop_row_induction M (source_row_wf M)).
  - exists (source_row_wf_formula $0),(fun _ => zeroM M). intro x.
    symmetry. apply source_row_wf_formula_correct.
  - intros x H. exact (proj1 H).
  - intros x p Hp H. exact (proj1 H).
  - intros x p q Hp Hq H. exact (proj1 H).
Qed.

Theorem source_prop_prv_wellformed M b c n f :
  source_prop_prv M b c n f -> source_sequent_wf M b c n f.
Proof.
  intros [r [Hr Hd]]. exact (source_sequent_wf_from_row M b c n f r Hr (source_prop_row_wellformed M r Hd)).
Qed.
Theorem source_prop_branches_wellformed M b c n a d f :
  source_prop_branches M b c n a d f -> source_branches_wf M b c n a d f.
Proof.
  intros [r [Hr Hd]]. exact (source_branches_wf_from_row M b c n a d f r Hr (source_prop_row_wellformed M r Hd)).
Qed.

Theorem source_prv_Ctx M b c n f :
  source_sequent_wf M b c n f ->
  (context_member M b c n f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw H0.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply trace_derives_base. apply source_prop_trace_base.
  split.
  - left. exists b,c,n,f. auto.
  -  left.
    exists b,c,n,f. repeat first [assumption | split].
Qed.

Theorem source_prv_Pc M b c n a d x y f :
  source_sequent_wf M b c n f ->
  (sf_relation M SFImpl a d x) ->
  (sf_relation M SFImpl x a y) ->
  (sf_relation M SFImpl y a f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw H0 H1 H2.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply trace_derives_base. apply source_prop_trace_base.
  split.
  - left. exists b,c,n,f. auto.
  - right.
    exists b,c,n,a,d,x,y,f. repeat first [assumption | split].
Qed.

Theorem source_prv_II M b c n a d f u v l :
  source_sequent_wf M b c n f ->
  source_prop_prv M u v l d ->
  (environment_cons M b c n a u v l) ->
  (sf_relation M SFImpl a d f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]] H0 H1.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,f. auto.
  -  left.
    exists b,c,n,a,d,f,u,v,l. repeat first [assumption | split].
Qed.

Theorem source_prv_Exp M b c n f :
  source_sequent_wf M b c n f ->
  source_prop_prv M b c n (zeroM M) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]].
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,f. auto.
  - right. left.
    exists b,c,n,f. repeat first [assumption | split].
Qed.

Theorem source_prv_CE1 M b c n a d f :
  source_sequent_wf M b c n a ->
  source_prop_prv M b c n f ->
  (sf_relation M SFAnd a d f) ->
  source_prop_prv M b c n a.
Proof.
  intros Hw [p [Hp Hdp]] H0.
  destruct (source_sequent_total M b c n a) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,a. auto.
  - right. right. left.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_CE2 M b c n a d f :
  source_sequent_wf M b c n d ->
  source_prop_prv M b c n f ->
  (sf_relation M SFAnd a d f) ->
  source_prop_prv M b c n d.
Proof.
  intros Hw [p [Hp Hdp]] H0.
  destruct (source_sequent_total M b c n d) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,d. auto.
  - right. right. right. left.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_DI1 M b c n a d f :
  source_sequent_wf M b c n f ->
  source_prop_prv M b c n a ->
  (sf_relation M SFOr a d f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]] H0.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,f. auto.
  - right. right. right. right. left.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_DI2 M b c n a d f :
  source_sequent_wf M b c n f ->
  source_prop_prv M b c n d ->
  (sf_relation M SFOr a d f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]] H0.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_unary M source_propositional_rules r p Hdp).
  apply source_prop_trace_unary.
  split.
  - left. exists b,c,n,f. auto.
  - right. right. right. right. right.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_IE M b c n a d f :
  source_sequent_wf M b c n d ->
  source_prop_prv M b c n f ->
  source_prop_prv M b c n a ->
  (sf_relation M SFImpl a d f) ->
  source_prop_prv M b c n d.
Proof.
  intros Hw [p [Hp Hdp]] [q [Hq Hdq]] H0.
  destruct (source_sequent_total M b c n d) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_binary M source_propositional_rules r p q Hdp Hdq).
  apply source_prop_trace_binary.
  split.
  - left. exists b,c,n,d. auto.
  -  left.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_CI M b c n a d f :
  source_sequent_wf M b c n f ->
  source_prop_prv M b c n a ->
  source_prop_prv M b c n d ->
  (sf_relation M SFAnd a d f) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]] [q [Hq Hdq]] H0.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_binary M source_propositional_rules r p q Hdp Hdq).
  apply source_prop_trace_binary.
  split.
  - left. exists b,c,n,f. auto.
  - right. left.
    exists b,c,n,a,d,f. repeat first [assumption | split].
Qed.

Theorem source_prv_BranchPair M b c n a d f u v l x y z :
  source_branches_wf M b c n a d f ->
  source_prop_prv M u v l f ->
  source_prop_prv M x y z f ->
  (environment_cons M b c n a u v l) ->
  (environment_cons M b c n d x y z) ->
  source_prop_branches M b c n a d f.
Proof.
  intros Hw [p [Hp Hdp]] [q [Hq Hdq]] H0 H1.
  destruct (source_branches_total M b c n a d f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_binary M source_propositional_rules r p q Hdp Hdq).
  apply source_prop_trace_binary.
  split.
  - right. exists b,c,n,a,d,f. auto.
  - right. right. left.
    exists b,c,n,a,d,f,u,v,l,x,y,z. repeat first [assumption | split].
Qed.

Theorem source_prv_DE M b c n a d f disj :
  source_sequent_wf M b c n f ->
  source_prop_prv M b c n disj ->
  source_prop_branches M b c n a d f ->
  (sf_relation M SFOr a d disj) ->
  source_prop_prv M b c n f.
Proof.
  intros Hw [p [Hp Hdp]] [q [Hq Hdq]] H0.
  destruct (source_sequent_total M b c n f) as [r Hr].
  exists r. split; [exact Hr|].
  apply (trace_derives_binary M source_propositional_rules r p q Hdp Hdq).
  apply source_prop_trace_binary.
  split.
  - left. exists b,c,n,f. auto.
  - right. right. right.
    exists b,c,n,a,d,f,disj. repeat first [assumption | split].
Qed.

Theorem source_prv_DE_three M b c n a d f disj u v l x y z :
  source_sequent_wf M b c n f -> source_branches_wf M b c n a d f ->
  source_prop_prv M b c n disj ->
  source_prop_prv M u v l f -> source_prop_prv M x y z f ->
  environment_cons M b c n a u v l -> environment_cons M b c n d x y z ->
  sf_relation M SFOr a d disj -> source_prop_prv M b c n f.
Proof.
  intros Hf Hbranches Hdisj Hleft Hright Hcl Hcr Hor.
  exact (source_prv_DE M b c n a d f disj Hf Hdisj
    (source_prv_BranchPair M b c n a d f u v l x y z Hbranches Hleft Hright Hcl Hcr) Hor).
Qed.
