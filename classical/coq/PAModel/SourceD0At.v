(** One hierarchy level captures the witnesses to an arbitrary source
    matrix. The level set is inserted before the matrix's outer parameters. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceRelativizationBounds SourceFiniteCutoffShift SourceQfFunctionality
  SourceHierarchySyntax SourceEwMonotone SourceD0Recipe SourceRelativizationRules
  SourceRelativizationFunctionality.
Unset Implicit Arguments.

Definition source_d0_at M domain phi d out :=exists shifted level ew point,
  source_cutoff_shift M 1 phi shifted /\source_LL_instance M (succM M d) (zeroM M) level /\
  source_ew_at M domain shifted (zeroM M) ew /\sf_relation M SFImpl level ew point /\
  sf_relation M SFAll point (zeroM M) out.

Theorem source_d0_at_total M domain phi d :exists out,source_d0_at M domain phi d out.
Proof.
  destruct (source_cutoff_shift_total M 1 phi) as (shifted&HS).
  destruct (source_LL_instance_total M (succM M d) (zeroM M)) as (level&HL).
  destruct (source_ew_recipe_total M domain shifted) as (ew&HE).
  destruct (sf_relation_total M SFImpl level ew) as (point&HP).
  destruct (sf_relation_total M SFAll point (zeroM M)) as (out&HO).
  exists out,shifted,level,ew,point. split;[exact HS|]. split;[exact HL|].
  split;[exact HE|]. split;assumption.
Qed.

Theorem source_d0_at_functional M domain phi d f g :
  source_d0_at M domain phi d f ->source_d0_at M domain phi d g ->f=g.
Proof.
  intros (s&l&e&p&HS&HL&HE&HP&HF) (s'&l'&e'&p'&HS'&HL'&HE'&HP'&HG).
  pose proof (source_cutoff_shift_functional M 1 phi s s' HS HS') as E. subst s'.
  pose proof (source_LL_instance_functional M (succM M d) (zeroM M) l l' HL HL') as E. subst l'.
  pose proof (source_ew_recipe_functional M domain s e e' HE HE') as E. subst e'.
  pose proof (sf_relation_functional M SFImpl l e p p' HP HP') as E. subst p'.
  exact (sf_relation_functional M SFAll p (zeroM M) f g HF HG).
Qed.

Theorem source_d0_at_bounded M domain phi d out k :
  source_bounded M domain (code_numeral M 1) ->source_bounded M phi (succM M k) ->
  coding_lt M d k ->source_d0_at M domain phi d out ->source_bounded M out k.
Proof.
  intros HD HB HName (s&l&e&p&HS&HL&HE&HP&HO).
  pose proof (source_cutoff_shift_bounded M 1 phi s k HB HS) as HBS.
  apply (proj2 (source_bounded_accept_unary M SFAll p out k (or_introl eq_refl) HO)).
  apply (proj2 (source_bounded_accept_binary M SFImpl l e p (succM M k)
    (or_intror (or_intror eq_refl)) HP)). split.
  - exact (source_LL_instance_bounded M (succM M d) (zeroM M) l (succM M k)
      (proj2 (coding_lt_succ_cancel M d k) HName) (coding_zero_lt_succ M k) HL).
  - exact (source_ew_recipe_bounded M domain s e k HD HBS HE).
Qed.

Print Assumptions source_d0_at_total.
Print Assumptions source_d0_at_functional.
Print Assumptions source_d0_at_bounded.
