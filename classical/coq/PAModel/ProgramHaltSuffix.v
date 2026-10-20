(** A realized contradiction code makes the seeded numerical search halt.
    The suffix and its two preparatory transitions are checked directly. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
 SearchStep KernelSafety RunSyntax NumericalReachability NumericalSearchDrain ProgramRealizability
 NumericalRuntime RuntimeFiniteMacros ProgramCandidateExecution.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Section HaltSuffix.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation N := (code_numeral M).
Variable P:D->D->D.
Variable U:D->D*D.
Variable E:D->D->bool.
Hypothesis HP:forall a b,pair_graph M a b(P a b).
Hypothesis HU:forall z,pair_graph M(fst(U z))(snd(U z))z.
Hypothesis HE:forall a b,E a b=true <->a=b.
Local Opaque runtime_wim runtime_bundle macro_r1 macro_r2 macro_r3
 macro_r4 macro_r5 macro_r6 macro_r7 macro_r8 macro_gen.

Definition program_halt_suffix : list(runtime_command M) :=
 [Rdrop M;Rnip M;Rnip M].

Lemma program_halt_suffix_exec w :
 runtime_exec M P U E program_halt_suffix(N 1,w,O,O)=None.
Proof.
 unfold program_halt_suffix.
 rewrite(macro_ex_drop M P U E (N 1)w O O).
 rewrite(macro_ex_nip M P U E HP HU HE O(N 1)w O O [Rnip M])
   by apply zero_ne_succ.
 cbn [runtime_exec runtime_step].
 rewrite(proj2(HE(N 1)(N 1))eq_refl). reflexivity.
Qed.

Theorem program_realizes_one_halts_runtime :
 program_realizes M(N 1) -> numerical_halts_from M(seed_state M).
Proof.
 intro H.
 destruct(numerical_seed_executes_realized M(N 1)
   (runtime_program M P program_halt_suffix O)H)
   as[Hhalt|[candidate[w Hreach]]];[exact Hhalt|].
 eapply numerical_reaches_halts;[exact Hreach|].
 exact(runtime_exec_halts M P U E HP HU HE program_halt_suffix
   (N 1,w,O,O)O(succM M candidate)(program_halt_suffix_exec w)).
Qed.
End HaltSuffix.

Theorem program_realizes_one_halts M :
 program_realizes M(code_numeral M 1) -> numerical_halts_from M(seed_state M).
Proof.
 intro H. destruct(numerical_runtime_operations M)as[P[U[E[HP[HU HE]]]]].
 exact(program_realizes_one_halts_runtime M P U E HP HU HE H).
Qed.
Print Assumptions program_halt_suffix_exec.
Print Assumptions program_realizes_one_halts.
