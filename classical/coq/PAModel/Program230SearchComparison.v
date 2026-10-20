(** Reduction of the full compiler comparison to the two concrete main-loop
    contracts. All iteration lengths and all encoded histories are internal
    elements of an arbitrary PA model. The contracts remain explicit premises. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
 NumericalProofs SearchStep KernelSafety RunSyntax NumericalRunSmallHistories
 SearchTransitionTotal Program230Configurations Program230Histories
 Program230HistoryJoin Program230HistoryConstructors Program230InstructionFormula
 Program230HaltingSentence Program230SearchState Program230RootReady
 Program230SearchRealization Program230HistoryDeterminism.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Logic.Classical_Prop.
Unset Implicit Arguments.

Definition p230_halt_search_macro M :=
 forall s pc,program230_root_ready M pc -> enumerator_halt M s ->
 exists b c time,
 program230_history M p230_instruction_formula b c time
   (p230_search_embedding (zeroM M) pc s) /\ p230_counter_halt_at M b c time.

Definition p230_numerical_search_halts M :=
 exists b c N,numerical_run M b c N /\ halt_at M b c N.

Definition p230_joint_prefix M n :=
 exists b c s,numerical_run M b c n /\ state_at M b c n s /\
   p230_search_state_realized M n s.

Lemma p230_eval_lift8 M rho a b c d e f g h t:
 evalM M (h.:g.:f.:e.:d.:c.:b.:a.:rho) (program230_lift 8 t)=evalM M rho t.
Proof. unfold evalM;cbn [program230_lift];rewrite !eval_up;reflexivity. Qed.

Definition p230_joint_prefix_formula(n:term):form :=
 ∃∃∃∃∃∃∃∃(run_formula $7 $6 (program230_lift 8 n) ∧
 (state_at_formula $7 $6 (program230_lift 8 n) $5 $4 $3 $2 $1 $0 ∧
 p230_search_state_realized_formula (program230_lift 8 n)
   (mkSearchState term $5 $4 $3 $2 $1 $0))).

Local Opaque holds run_formula state_at_formula p230_search_state_realized_formula.

Theorem p230_joint_prefix_formula_correct M rho n:
 holds M rho (p230_joint_prefix_formula n)<->p230_joint_prefix M (evalM M rho n).
Proof.
 unfold p230_joint_prefix_formula,p230_joint_prefix.
 repeat setoid_rewrite holds_ex. repeat setoid_rewrite holds_and.
 setoid_rewrite run_formula_correct. setoid_rewrite state_at_formula_correct.
 setoid_rewrite p230_search_state_realized_formula_correct.
 setoid_rewrite p230_eval_lift8.
 split.
 -intros [b [c [pl [np [tw [ws [d [h H]]]]]]]].
  exists b,c,(mkSearchState (carrier M) pl np tw ws d h);exact H.
 -intros [b [c [[pl np tw ws d h] H]]].
  exists b,c,pl,np,tw,ws,d,h;exact H.
Qed.

Lemma p230_joint_prefix_definable M:Definable1 M (p230_joint_prefix M).
Proof.
 exists (p230_joint_prefix_formula $0),(fun _ => zeroM M).
 intro n;symmetry;apply p230_joint_prefix_formula_correct.
Qed.

Theorem p230_nonhalting_search_joint_prefixes M:
 p230_normal_search_macro M -> ~p230_numerical_search_halts M ->
 forall n,p230_joint_prefix M n.
Proof.
 intros Hnormal Hno.
 apply (definable_induction M (p230_joint_prefix M) (p230_joint_prefix_definable M)).
 -destruct (numerical_run_from_zero M (seed_state M)) as [b [c [HR HS]]].
  exists b,c,(seed_state M);split;[exact HR|].
  split;[exact HS|apply p230_realized_seed].
 -intros n [b [c [s [HR [HS HP]]]]].
  destruct (numerical_search_step_or_halt M s) as [[t Hstep]|Hhalt].
  +destruct (numerical_run_from_extend M b c n (seed_state M) s t HR HS Hstep)
     as [d [e [HD [HT Hpreserved]]]].
   exists d,e,t;split;[exact HD|].
   split;[exact HT|exact (p230_realized_search_step M Hnormal n s t HP Hstep)].
  +exfalso;apply Hno;exists b,c,n;split;[exact HR|].
   exists s;split;assumption.
Qed.

Theorem p230_nonhalting_search_counter_nonhalting M:
 p230_normal_search_macro M -> ~p230_numerical_search_halts M -> p230_counter_nonhalting M.
Proof.
 intros Hnormal Hno [b [c [N [HR HH]]]].
 destruct (p230_nonhalting_search_joint_prefixes M Hnormal Hno (succM M N))
   as [d [e [s [HD [HS [f [g [time [pc [HF [HT [Hpc Hlength]]]]]]]]]]]].
 exact (p230_history_halt_is_maximal M b c f g N time (p230_initial_configuration M)
   HR HH HF (proj1 (coding_lt_succ_cancel M N time) Hlength)).
Qed.

Theorem p230_halting_search_counter_halting M:
 p230_normal_search_macro M -> p230_halt_search_macro M ->
 p230_numerical_search_halts M -> p230_counter_halting M.
Proof.
 intros Hnormal Hhalt [b [c [N [HR [s [HS HH]]]]]].
 destruct (p230_numerical_run_realization M Hnormal b c N HR s HS)
   as [d [e [time [pc [HD [HT [Hpc Hbound]]]]]]].
 destruct (Hhalt s pc Hpc HH) as [f [g [duration [HF [last [HL Hlast]]]]]].
 destruct (program230_history_join M p230_instruction_formula d e time f g duration
   (p230_initial_configuration M) (p230_search_embedding (zeroM M) pc s) HD HT HF)
   as [u [v [HU [Hleft Hright]]]].
 exists u,v,(addM M time duration);split;[exact HU|].
 exists last;split;[|exact Hlast].
 exact (proj1 (Hright duration last (coding_lt_succ M duration)) HL).
Qed.

Theorem p230_counter_numerical_search_equivalence_from_macros M:
 p230_normal_search_macro M -> p230_halt_search_macro M ->
 (p230_counter_halting M <-> p230_numerical_search_halts M).
Proof.
 intros Hnormal Hhalt;split.
 -intro HH;apply NNPP;intro Hno.
  exact (p230_nonhalting_search_counter_nonhalting M Hnormal Hno HH).
 -exact (p230_halting_search_counter_halting M Hnormal Hhalt).
Qed.

Print Assumptions p230_joint_prefix_formula_correct.
Print Assumptions p230_joint_prefix_definable.
Print Assumptions p230_nonhalting_search_joint_prefixes.
Print Assumptions p230_nonhalting_search_counter_nonhalting.
Print Assumptions p230_halting_search_counter_halting.
Print Assumptions p230_counter_numerical_search_equivalence_from_macros.
