(** Modus ponens on arbitrary internally coded continuation blocks. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
  NumericalProofs SearchStep NumericalCommands NumericalReachability
  NumericalSearchDrain ProgramRealizability NumericalRuntime RuntimeFiniteMacros.
From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.

Section MPCompiler.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation N := (code_numeral M).
Variable P : D -> D -> D.
Variable U : D -> D * D.
Variable E : D -> D -> bool.
Hypothesis HP : forall a b, pair_graph M a b (P a b).
Hypothesis HU : forall z, pair_graph M (fst (U z)) (snd (U z)) z.
Hypothesis HE : forall a b, E a b = true <-> a = b.
Local Notation Exec := (runtime_exec M P U E).
Lemma mp_runtime_code a b h : implication_graph M a b h ->
  runtime_wim M P a b = h.
Proof.
  intro Himp. apply (code_relation_functional M (E_wim (CEvar 0) (CEvar 1))
    (search_values M [a;b]) (runtime_wim M P a b) h).
  - exact (runtime_value_graph M P HP _ _).
  - exact Himp.
Qed.
Local Opaque runtime_wim runtime_bundle macro_r1 macro_r2 macro_r3 macro_r4
  macro_r5 macro_r6 macro_r7 macro_r8 macro_gen.

Definition mp_suffix (b : D) : list (runtime_command M) :=
  [Rnip M; Rdrop M; Rnip M; Rcmp M b; Rax M b O O O] ++
  repeat (Rnip M) 10 ++ [Rdrop M; Rnip M; Rnip M].

Lemma mp_nip_one t w d L :
  Exec (Rnip M :: L) (t,w,d,N 1) = None.
Proof.
  cbn [runtime_exec runtime_step].
  rewrite (proj2 (HE (N 1) (N 1)) eq_refl). reflexivity.
Qed.

Lemma mp_suffix_exec a b h w : implication_graph M a b h ->
  Exec (mp_suffix b) (h,P a w,O,O) = None \/
  Exec (mp_suffix b) (h,P a w,O,O) = Some (b,w,O,O).
Proof.
  intro Himp.
  assert (Hcode : runtime_wim M P a b = h).
  { exact (mp_runtime_code a b h Himp). }
  unfold mp_suffix. cbn [app].
  rewrite (macro_ex_nip M P U E HP HU HE) by apply zero_ne_succ.
  rewrite (macro_ex_drop M P U E).
  destruct (E a (N 1)) eqn:Ha.
  - apply HE in Ha. subst a. left. apply mp_nip_one.
  - apply (runtime_eq_false M E HE) in Ha.
    rewrite (macro_ex_nip M P U E HP HU HE) by exact Ha.
    rewrite (macro_ex_mp_ok M P U E HE).
    2: { rewrite coding_add_zero. exact Hcode. }
    repeat first [progress cbn [repeat app]
      | rewrite (macro_ex_drop M P U E)
      | rewrite (macro_ex_ax M P U E)
      | rewrite (macro_ex_nip M P U E HP HU HE) by
          first [apply (macro_gate_ne1 M P E HP HE)
                |apply (macro_row1_ne1 M P HP)
                |apply (macro_row2_ne1 M P HP)
                |apply (macro_row3_ne1 M P HP)
                |apply (macro_row4_ne1 M P HP)
                |apply (macro_row5_ne1 M P HP)
                |apply (macro_row6_ne1 M P HP)
                |apply (macro_row7_ne1 M P HP)
                |apply (macro_row8_ne1 M P HP)
                |apply (macro_gen_ne1 M P HP)
                |apply zero_ne_succ]
      | rewrite (macro_stack_expand M P)
      | rewrite (macro_gate_same M P E HE)
      | rewrite coding_add_zero_r | rewrite coding_add_zero].
    destruct (E b (N 1)) eqn:Hb.
    + apply HE in Hb. subst b. left. apply mp_nip_one.
    + apply (runtime_eq_false M E HE) in Hb.
      rewrite (macro_ex_nip M P U E HP HU HE) by exact Hb.
      rewrite (macro_ex_nip M P U E HP HU HE) by apply zero_ne_succ.
      right. reflexivity.
Qed.

Theorem program_realizes_mp_with_runtime a b h :
  program_realizes M a -> program_realizes M h ->
  implication_graph M a b h -> program_realizes M b.
Proof.
  intros HA HH Himp tail.
  set (suffix := runtime_program M P (mp_suffix b) tail).
  destruct (HH suffix) as [ph Hh].
  set (drop := runtime_program M P [Rdrop M] ph).
  destruct (HA drop) as [pa Ha].
  exists pa. intros np t w.
  destruct (Ha np t w) as [Hhalt|Hreach]; [now left|].
  assert (Hdrop : numerical_reaches M
    (mkSearchState D drop np a w O O)
    (mkSearchState D ph np O (P a w) O O)).
  { exact (runtime_exec_reaches M P U E HP HU HE [Rdrop M]
      (a,w,O,O) (O,P a w,O,O) ph np eq_refl). }
  assert (Hprefix : numerical_reaches M
    (mkSearchState D pa np t w O O)
    (mkSearchState D ph np O (P a w) O O)).
  { eapply numerical_reaches_transitive; eassumption. }
  destruct (Hh np O (P a w)) as [Hhalt|HreachH].
  - left. eapply numerical_reaches_halts; eassumption.
  - assert (HprefixH : numerical_reaches M
      (mkSearchState D pa np t w O O)
      (mkSearchState D suffix np h (P a w) O O)).
    { eapply numerical_reaches_transitive; eassumption. }
    destruct (mp_suffix_exec a b h w Himp) as [Hhalt|Hend].
    + left. eapply numerical_reaches_halts; [exact HprefixH|].
      exact (runtime_exec_halts M P U E HP HU HE (mp_suffix b)
        (h,P a w,O,O) tail np Hhalt).
    + right. eapply numerical_reaches_transitive; [exact HprefixH|].
      exact (runtime_exec_reaches M P U E HP HU HE (mp_suffix b)
        (h,P a w,O,O) (b,w,O,O) tail np Hend).
Qed.
End MPCompiler.

Theorem program_realizes_modus_ponens M a b h :
  program_realizes M a -> program_realizes M h ->
  implication_graph M a b h -> program_realizes M b.
Proof.
  destruct (numerical_runtime_operations M) as [P [U [E [HP [HU HE]]]]].
  exact (program_realizes_mp_with_runtime M P U E HP HU HE a b h).
Qed.

Print Assumptions mp_suffix_exec.
Print Assumptions program_realizes_mp_with_runtime.
Print Assumptions program_realizes_modus_ponens.
