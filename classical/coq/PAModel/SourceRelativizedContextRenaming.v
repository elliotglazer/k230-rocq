(** The exact-length context maps inherit the internal formula-level
    commuting square.  No host-language list enumerates the source context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions
  NumericalContexts NumericalContextRenaming NumericalRenaming SourceBounded
  SourceRelativization SourceRelativizationFunctionality
  SourceRelativizationRenaming SourceRelativizedContexts.
Unset Implicit Arguments.

Theorem source_context_relativization_renaming M domain b c n u v
    p q m delta b' c' u' v' :
  source_bounded M domain (code_numeral M 1) ->
  source_context_relativization M domain b c n u v ->
  context_renaming M b c n p q m delta b' c' ->
  context_renaming M u v n p q m delta u' v' ->
  source_context_relativization M domain b' c' n u' v'.
Proof.
  intros HD HR HS HT i f' r' HI HF' HR'.
  destruct (beta_total M b c i) as [f HF].
  destruct (beta_total M u v i) as [r HOrigR].
  exact (source_relativization_renaming M domain f r p q m delta f' r'
    HD (HR i f r HI HF HOrigR) (HS i f f' HI HF HF')
    (HT i r r' HI HOrigR HR')).
Qed.

Theorem source_context_renaming_relativization M domain b c n u v
    p q m delta b' c' u' v' :
  source_bounded M domain (code_numeral M 1) ->
  source_context_relativization M domain b c n u v ->
  context_renaming M b c n p q m delta b' c' ->
  source_context_relativization M domain b' c' n u' v' ->
  context_renaming M u v n p q m delta u' v'.
Proof.
  intros HD HR HS HT i r r' HI HOrigR HR'.
  destruct (beta_total M b c i) as [f HF].
  destruct (beta_total M b' c' i) as [f' HF'].
  destruct (source_relativization_renaming_exists M f domain p q m delta f' r
    HD (HS i f f' HI HF HF') (HR i f r HI HF HOrigR)) as [s [HRS HNS]].
  rewrite (source_relativization_functional M f' domain r' s
    (HT i f' r' HI HF' HR') HRS). exact HNS.
Qed.

Corollary source_context_relativization_shift M domain b c n u v b' c' u' v' :
  source_bounded M domain (code_numeral M 1) ->
  source_context_relativization M domain b c n u v ->
  context_shift M b c n b' c' -> context_shift M u v n u' v' ->
  source_context_relativization M domain b' c' n u' v'.
Proof.
  intros HD HR HS HT. exact (source_context_relativization_renaming M domain b c n u v
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) b' c' u' v' HD HR HS HT).
Qed.

Corollary source_context_shift_relativization M domain b c n u v b' c' u' v' :
  source_bounded M domain (code_numeral M 1) ->
  source_context_relativization M domain b c n u v ->
  context_shift M b c n b' c' ->
  source_context_relativization M domain b' c' n u' v' ->
  context_shift M u v n u' v'.
Proof.
  intros HD HR HS HT. exact (source_context_renaming_relativization M domain b c n u v
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) b' c' u' v' HD HR HS HT).
Qed.

Print Assumptions source_context_relativization_renaming.
Print Assumptions source_context_renaming_relativization.
Print Assumptions source_context_relativization_shift.
Print Assumptions source_context_shift_relativization.
