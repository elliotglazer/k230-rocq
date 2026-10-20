(** PA-definable composition of complete search steps into actual instruction
    histories. The normal-step premise is explicit: the concrete main-loop
    implementation must supply it before any machine/search equivalence follows. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalProofs SearchStep KernelSafety RunSyntax Program230Configurations
 Program230Histories Program230HistoryJoin Program230HistoryConstructors
 Program230InstructionFormula Program230HaltingSentence Program230SearchState
 Program230RootReady.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import setoid_ring.Ring.
Unset Implicit Arguments.

Definition p230_normal_search_macro M :=
 forall s t pc,program230_root_ready M pc -> enumerator_step M s t ->
 exists b c time pc',
 program230_history M p230_instruction_formula b c time
   (p230_search_embedding (zeroM M) pc s) /\
 program230_state_at M b c time (p230_search_embedding (zeroM M) pc' t) /\
 program230_root_ready M pc' /\ coding_lt M (zeroM M) time.

Definition p230_search_state_realized M n s :=
 exists b c time pc,
 program230_history M p230_instruction_formula b c time (p230_initial_configuration M) /\
 program230_state_at M b c time (p230_search_embedding (zeroM M) pc s) /\
 program230_root_ready M pc /\ coding_lt M n (succM M time).

Definition p230_lift_search n (s:search_state term):search_state term :=
 mkSearchState term (program230_lift n (search_pl s)) (program230_lift n (search_np s))
 (program230_lift n (search_tw s)) (program230_lift n (search_ws s))
 (program230_lift n (search_d s)) (program230_lift n (search_h s)).

Lemma p230_eval_search_is_term_value M rho s:
 p230_eval_search M rho s=term_state_value M rho s.
Proof. destruct s;reflexivity. Qed.

Lemma p230_eval_lift4 M rho a b c d t:
 evalM M (d.:c.:b.:a.:rho) (program230_lift 4 t)=evalM M rho t.
Proof. unfold evalM;cbn [program230_lift];rewrite !eval_up;reflexivity. Qed.

Lemma p230_lift_search4_correct M rho a b c d s:
 p230_eval_search M (d.:c.:b.:a.:rho) (p230_lift_search 4 s)=term_state_value M rho s.
Proof.
 destruct s;unfold p230_eval_search,p230_lift_search,term_state_value;cbn.
 unfold evalM;cbn [program230_lift];try rewrite !eval_up;reflexivity.
Qed.

Definition p230_search_state_realized_formula(n:term)(s:search_state term):form :=
 ∃∃∃∃(program230_history_formula p230_instruction_formula $3 $2 $1 p230_initial_terms ∧
 (program230_state_at_formula $3 $2 $1
    (p230_search_embedding zero $0 (p230_lift_search 4 s)) ∧
 (program230_root_ready_formula $0 ∧ Peano.sless (program230_lift 4 n) (σ $1)))).

Local Opaque holds program230_history_formula program230_state_at_formula
 program230_root_ready_formula.

Theorem p230_search_state_realized_formula_correct M rho n s:
 holds M rho (p230_search_state_realized_formula n s)<->
 p230_search_state_realized M (evalM M rho n) (term_state_value M rho s).
Proof.
 unfold p230_search_state_realized_formula,p230_search_state_realized.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite program230_history_formula_correct.
 setoid_rewrite program230_state_at_formula_correct.
 setoid_rewrite program230_root_ready_formula_correct.
 setoid_rewrite less_formula_correct.
 setoid_rewrite p230_initial_terms_correct.
 setoid_rewrite p230_search_embedding_eval.
 setoid_rewrite p230_lift_search4_correct.
 setoid_rewrite p230_eval_lift4. reflexivity.
Qed.

Definition p230_run_at_realized M b c k :=
 forall s,state_at M b c k s -> p230_search_state_realized M k s.

Definition p230_run_at_realized_formula(b c k:term):form :=
 ∀∀∀∀∀∀(state_at_formula (run_lift 6 b) (run_lift 6 c) (run_lift 6 k)
   $5 $4 $3 $2 $1 $0 →
 p230_search_state_realized_formula (run_lift 6 k) (mkSearchState term $5 $4 $3 $2 $1 $0)).

Local Opaque state_at_formula p230_search_state_realized_formula.

Theorem p230_run_at_realized_formula_correct M rho b c k:
 holds M rho (p230_run_at_realized_formula b c k)<->
 p230_run_at_realized M (evalM M rho b) (evalM M rho c) (evalM M rho k).
Proof.
 unfold p230_run_at_realized_formula,p230_run_at_realized.
 repeat setoid_rewrite holds_all. setoid_rewrite holds_imp.
 setoid_rewrite state_at_formula_correct.
 setoid_rewrite p230_search_state_realized_formula_correct.
 setoid_rewrite eval_run_lift6.
 split.
 -intros H [pl np tw ws d h] HS;exact (H pl np tw ws d h HS).
 -intros H pl np tw ws d h HS;exact (H (mkSearchState (carrier M) pl np tw ws d h) HS).
Qed.

Theorem p230_bounded_run_realized_definable M b c N:
 Definable1 M (fun k => coding_lt M k (succM M N) -> p230_run_at_realized M b c k).
Proof.
 exists (Peano.sless $0 (σ $3) → p230_run_at_realized_formula $1 $2 $0),
   (b.:c.:N.:(fun _ => zeroM M)).
 intro k;rewrite holds_imp,less_formula_correct,p230_run_at_realized_formula_correct;reflexivity.
Qed.

Lemma p230_positive_extension_bound M n time duration:
 coding_lt M n (succM M time) -> coding_lt M (zeroM M) duration ->
 coding_lt M (succM M n) (succM M (addM M time duration)).
Proof.
 intros Hn [r Er].
 apply (proj2 (coding_lt_succ_cancel M n (addM M time duration))).
 assert (Hextend:coding_lt M time (addM M time duration)).
 {exists r;rewrite Er,coding_add_zero.
  rewrite (Arithmetic.add_comm M time (succM M r)),(Arithmetic.add_succ M r time),
    (Arithmetic.add_comm M r time);reflexivity. }
 apply coding_lt_succ_cases in Hn;destruct Hn as [Hn|En].
 -exact (coding_lt_trans M n time (addM M time duration) Hn Hextend).
 -now rewrite En.
Qed.

Theorem p230_realized_seed M:
 p230_search_state_realized M (zeroM M) (seed_state M).
Proof.
 destruct (program230_history_zero M p230_instruction_formula (p230_initial_configuration M))
   as [b [c [HR HS]]].
 exists b,c,(zeroM M),(code_numeral M 1).
 split;[exact HR|]. split.
 -rewrite p230_initial_search_embedding;exact HS.
 -split;[apply program230_root_ready_initial|apply coding_zero_lt_succ].
Qed.

Theorem p230_realized_search_step M:
 p230_normal_search_macro M ->
 forall n s t,p230_search_state_realized M n s -> enumerator_step M s t ->
 p230_search_state_realized M (succM M n) t.
Proof.
 intros Hmacro n s t [b [c [time [pc [HR [HS [Hpc Htime]]]]]]] Hstep.
 destruct (Hmacro s t pc Hpc Hstep) as [d [e [duration [pc' [HD [HT [Hpc' Hduration]]]]]]].
 destruct (program230_history_join M p230_instruction_formula b c time d e duration
   (p230_initial_configuration M) (p230_search_embedding (zeroM M) pc s) HR HS HD)
   as [f [g [HF [HL Hright]]]].
 exists f,g,(addM M time duration),pc';split;[exact HF|]. split.
 -exact (proj1 (Hright duration _ (coding_lt_succ M duration)) HT).
 -split;[exact Hpc'|exact (p230_positive_extension_bound M n time duration Htime Hduration)].
Qed.

Theorem p230_numerical_run_realization M:
 p230_normal_search_macro M ->
 forall b c N,numerical_run M b c N -> p230_run_at_realized M b c N.
Proof.
 intros Hmacro b c N [Hstart Hsteps].
 assert (H:forall k,coding_lt M k (succM M N) -> p230_run_at_realized M b c k).
 {apply (definable_induction M
    (fun k => coding_lt M k (succM M N) -> p230_run_at_realized M b c k)
    (p230_bounded_run_realized_definable M b c N)).
  -intros _ s HS.
   assert (E:s=seed_state M) by (exact (state_at_functional M b c (zeroM M) s (seed_state M) HS Hstart)).
   subst s;apply p230_realized_seed.
  -intros k IH Hbound s HS.
   assert (Hk:coding_lt M k N) by (exact (proj1 (coding_lt_succ_cancel M k N) Hbound)).
   destruct (state_at_total M b c k) as [previous HP].
   eapply p230_realized_search_step;[exact Hmacro| |exact (Hsteps k previous s Hk HP HS)].
   apply IH;[exact (coding_lt_trans M k N (succM M N) Hk (coding_lt_succ M N))|exact HP]. }
 exact (H N (coding_lt_succ M N)).
Qed.

Print Assumptions p230_search_state_realized_formula_correct.
Print Assumptions p230_run_at_realized_formula_correct.
Print Assumptions p230_bounded_run_realized_definable.
Print Assumptions p230_positive_extension_bound.
Print Assumptions p230_realized_seed.
Print Assumptions p230_realized_search_step.
Print Assumptions p230_numerical_run_realization.
