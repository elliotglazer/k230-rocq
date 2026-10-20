(** PA formulas for arbitrary-start search histories and their reachability. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT NumericalProofs
  SearchStep RunSyntax.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition run_from_formula (b c n : term) (s : search_state term) : form :=
  state_at_formula b c zero (search_pl s) (search_np s) (search_tw s)
    (search_ws s) (search_d s) (search_h s) ∧ run_transition_formula b c n.

Lemma run_from_formula_correct M rho b c n s :
  holds M rho (run_from_formula b c n s) <->
  numerical_run_from M (evalM M rho b) (evalM M rho c) (evalM M rho n)
    (term_state_value M rho s).
Proof.
  unfold run_from_formula,numerical_run_from.
  rewrite holds_and,state_at_formula_correct,run_transition_formula_correct.
  reflexivity.
Qed.

Local Opaque holds run_from_formula state_at_formula run_transition_formula.

Definition numerical_reaches M (s t : search_state (carrier M)) : Prop :=
  exists b c n, numerical_run_from M b c n s /\ state_at M b c n t.
Definition numerical_halts_from M (s : search_state (carrier M)) : Prop :=
  exists b c n, numerical_run_from M b c n s /\ halt_at M b c n.

Definition lift_state (n : nat) (s : search_state term) : search_state term :=
  mkSearchState term (run_lift n (search_pl s)) (run_lift n (search_np s))
    (run_lift n (search_tw s)) (run_lift n (search_ws s))
    (run_lift n (search_d s)) (run_lift n (search_h s)).

Lemma lift_state3_correct M rho a b c s :
  term_state_value M (c .: b .: a .: rho) (lift_state 3 s)=term_state_value M rho s.
Proof.
  destruct s; unfold term_state_value,lift_state; cbn -[run_lift].
  f_equal; apply lift3_correct.
Qed.

Lemma lift_state6_correct M rho a b c d e f s :
  term_state_value M (f .: e .: d .: c .: b .: a .: rho) (lift_state 6 s)=term_state_value M rho s.
Proof.
  destruct s; unfold term_state_value,lift_state; cbn -[run_lift].
  f_equal;apply eval_run_lift6.
Qed.

Definition reach_formula (s t : search_state term) : form :=
  let s' := lift_state 3 s in let t' := lift_state 3 t in
  ∃∃∃ (run_from_formula $2 $1 $0 s' ∧
    state_at_formula $2 $1 $0 (search_pl t') (search_np t') (search_tw t')
      (search_ws t') (search_d t') (search_h t')).

Lemma reach_formula_correct M rho s t :
  holds M rho (reach_formula s t) <->
  numerical_reaches M (term_state_value M rho s) (term_state_value M rho t).
Proof.
  unfold reach_formula,numerical_reaches.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite run_from_formula_correct. setoid_rewrite state_at_formula_correct.
  setoid_rewrite lift_state3_correct. reflexivity.
Qed.

Definition halts_from_formula (s : search_state term) : form :=
  ∃∃∃ (run_from_formula $2 $1 $0 (lift_state 3 s) ∧ halt_at_formula $2 $1 $0).

Lemma halts_from_formula_correct M rho s :
  holds M rho (halts_from_formula s) <->
  numerical_halts_from M (term_state_value M rho s).
Proof.
  unfold halts_from_formula,numerical_halts_from.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite run_from_formula_correct. setoid_rewrite halt_at_formula_correct.
  setoid_rewrite lift_state3_correct. reflexivity.
Qed.

Definition bound_state : search_state term :=mkSearchState term $5 $4 $3 $2 $1 $0.
Definition numerical_drains M (s : search_state (carrier M)) : Prop :=
  numerical_halts_from M s \/ exists t, numerical_reaches M s t /\
    search_pl t=zeroM M /\ search_np t=search_np s.

Definition drains_formula (s : search_state term) : form :=
  halts_from_formula s ∨ ∃∃∃∃∃∃
    (reach_formula (lift_state 6 s) bound_state ∧
      (search_pl bound_state == zero ∧ search_np bound_state ==run_lift 6 (search_np s))).

Lemma drains_formula_correct M rho s :
  holds M rho (drains_formula s) <-> numerical_drains M (term_state_value M rho s).
Proof.
  unfold drains_formula,numerical_drains.
  rewrite holds_or,halts_from_formula_correct.
  repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
  setoid_rewrite reach_formula_correct. setoid_rewrite lift_state6_correct.
  split.
  - intros [H|[pl [np [tw [ws [d [h [Hr [Hp Hn]]]]]]]]];[now left|].
    right. exists (mkSearchState (carrier M) pl np tw ws d h).
    split;[exact Hr|]. split;[exact Hp|].
    change (np=evalM M (h .: d .: ws .: tw .: np .: pl .: rho) (run_lift 6 (search_np s))) in Hn.
    now rewrite eval_run_lift6 in Hn.
  - intros [H|[t [Hr [Hp Hn]]]];[now left|].
    destruct t as [pl np tw ws d h]. right. exists pl,np,tw,ws,d,h.
    split;[exact Hr|]. split;[exact Hp|].
    change (np=evalM M (h .: d .: ws .: tw .: np .: pl .: rho) (run_lift 6 (search_np s))).
    now rewrite eval_run_lift6.
Qed.

Lemma numerical_drains_definable M :
  Definable1 M (fun k => forall s, search_pl s=k ->numerical_drains M s).
Proof.
  exists (∀∀∀∀∀∀ (search_pl bound_state==$6 →drains_formula bound_state)),
    (fun _=>zeroM M).
  intro k. symmetry. repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
  setoid_rewrite drains_formula_correct.
  split.
  - intros H [pl np tw ws d h] Hp. exact (H pl np tw ws d h Hp).
  - intros H pl np tw ws d h Hp. exact (H (mkSearchState (carrier M) pl np tw ws d h) Hp).
Qed.

Print Assumptions reach_formula_correct.
Print Assumptions numerical_drains_definable.






