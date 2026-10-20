(** Actual existential elimination packages a witness implication into an
    implication from existence, preserving an arbitrary closed context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming
  NumericalRenaming NumericalSourceFull SourceQuantifierRules SourceProofWeakening
  SourceInstantiationConstructors SourceClosedContextShift SourceImplicationAllShift SourceTraceBounds
  SourceLeastOrdinalWitness.
Unset Implicit Arguments.

Theorem source_full_exists_implication M b c n k body ex target shifted witnessimp result :
  context_bounded M b c n (zeroM M) ->
  source_bounded M ex k ->source_bounded M target k ->
  sf_relation M SFEx body (zeroM M) ex ->source_formula_shift M target shifted ->
  sf_relation M SFImpl body shifted witnessimp ->sf_relation M SFImpl ex target result ->
  source_full_prv M b c n witnessimp ->source_full_prv M b c n result.
Proof.
  intros HC HE HT HEx HS HW HR PW.
  assert (HCk:context_bounded M b c n k).
  { exact (context_bounded_monotone M b c n (zeroM M) k HC (coding_zero_lt_succ M k)). }
  assert (HBody:source_bounded M body (succM M k)).
  { exact (proj1 (source_bounded_accept_unary M SFEx body ex k (or_intror eq_refl) HEx) HE). }
  assert (HShifted:source_bounded M shifted (succM M k)) by exact (source_shift_bound M target shifted k HT HS).
  assert (HResult:source_bounded M result k).
  { exact (proj2 (source_bounded_accept_binary M SFImpl ex target result k
      (or_intror (or_intror eq_refl)) HR) (conj HE HT)). }
  pose proof (source_closed_context_shift_self M b c n HC) as HSelf.
  destruct (numerical_renaming_total M ex (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1))
    as (exshift&HExShift).
  destruct (environment_cons_total M b c n ex) as (u&v&l&HCons).
  destruct (environment_cons_total M b c n exshift) as (s&t&l'&HConsShift).
  assert (EL:l'=l) by (rewrite (proj1 HConsShift),(proj1 HCons);reflexivity). subst l'.
  pose proof (context_renaming_cons M b c n (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    b c ex exshift u v l s t HSelf HExShift HCons HConsShift) as HContextShift.
  destruct (environment_cons_total M s t l body) as (x&y&m&HBranch).
  assert (HCurrent:context_bounded M u v l k).
  { exact (proj2 (context_bounded_cons M b c n ex u v l k HCons) (conj HE HCk)). }
  pose proof (context_shift_preserves_bound M u v l s t k HContextShift HCurrent) as HShiftContext.
  assert (HBranchBound:context_bounded M x y m (succM M k)).
  { exact (proj2 (context_bounded_cons M s t l body x y m _ HBranch) (conj HBody HShiftContext)). }
  assert (IBranch:context_included M b c n x y m).
  { intros f HF. apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HBranch f).
    exact (source_cons_tail_inclusion M _ _ _ _ _ _ _ HConsShift f HF). }
  assert (PBody:source_full_prv M x y m body).
  { apply full_source_Ctx;[exists (succM M k);auto|].
    apply (proj2 (context_member_cons M s t l body x y m body HBranch)). now left. }
  assert (PShifted:source_full_prv M x y m shifted).
  { exact (full_source_IE M x y m body shifted witnessimp
      (ex_intro _ (succM M k) (conj HShifted HBranchBound))
      (source_full_prv_weaken_bounded M b c n x y m _ _ PW IBranch HBranchBound) PBody HW). }
  assert (PEx:source_full_prv M u v l ex).
  { apply full_source_Ctx;[exists k;auto|].
    apply (proj2 (context_member_cons M b c n ex u v l ex HCons)). now left. }
  assert (PTarget:source_full_prv M u v l target).
  { exact (full_source_ExE M u v l body ex target shifted s t x y m
      (ex_intro _ k (conj HT HCurrent)) PEx PShifted HEx HContextShift HBranch HS). }
  exact (full_source_II M b c n ex target result u v l
    (ex_intro _ k (conj HResult HCk)) PTarget HCons HR).
Qed.

Print Assumptions source_full_exists_implication.
