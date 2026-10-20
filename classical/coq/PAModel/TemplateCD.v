(** The retained 107 condensed-detachment derivations from K230L/CD230.v,
    lifted syntactically to code expressions. They prove finite templates,
    not a statement about standard-number proofs only. The source derivations
    originate in the pinned Jeff/Huntsman calculus; no source theorem is used.
    Source SHA256: c788460c8dd0f4dda4440cae4595d73723223b385825d18df2bf94b52764d087. *)
From PAModel Require Import CodeExpressions ProofTemplates.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Section Templates.
Variable G : list (code_expr * code_expr).
Lemma tcd_0 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v2) (E_wim (E_wim v2 v0) (E_wim v3 v0))).
Proof. exact (template_r8 v2 v3 v0 v1). Qed.
Lemma tcd_1 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v1)) (E_wim v1 v3)) (E_wim v4 (E_wim v1 v3))).
Proof. exact (TP_mp _ _ (tcd_0 v1 v3 v0 v2) (tcd_0 (E_wim v1 v3) v0 (E_wim (E_wim v0 v1) (E_wim v2 v1)) v4)). Qed.
Lemma tcd_2 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v1 v2) (E_wim v2 (E_wim v1 v2)))).
Proof. exact (TP_mp _ _ (tcd_1 (CEconst 0) v2 v1 (E_wim v1 v2) (E_wim v1 v2)) (tcd_1 (E_wim (CEconst 0) v2) (E_wim v1 v2) v2 (E_wim v2 (E_wim v1 v2)) v0)). Qed.
Lemma tcd_3 (v0 v1 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim v1 (E_wim v0 v1))).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_2 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_4 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v0)) v1) (E_wim v2 v1)).
Proof. exact (TP_mp _ _ (tcd_3 v1 v0) (tcd_0 v1 v0 (E_wim v0 (E_wim v1 v0)) v2)). Qed.
Lemma tcd_5 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v2))) (E_wim v3 (E_wim v2 (E_wim v1 v2)))).
Proof. exact (TP_mp _ _ (tcd_4 v2 v1 v0) (tcd_0 (E_wim v2 (E_wim v1 v2)) v1 (E_wim v0 v1) v3)). Qed.
Lemma tcd_6 (v0 v1 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim v1 v1))).
Proof. exact (TP_mp _ _ (tcd_3 v1 v1) (tcd_5 v1 v1 v1 v0)). Qed.
Lemma tcd_7 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v0 v0)) v1) (E_wim v2 v1)).
Proof. exact (TP_mp _ _ (tcd_6 (E_wim v1 (CEconst 0)) v0) (tcd_0 v1 (CEconst 0) (E_wim v0 (E_wim v0 v0)) v2)). Qed.
Lemma tcd_8 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v1 v1) (E_wim v2 (E_wim v1 v1)))).
Proof. exact (TP_mp _ _ (tcd_7 v1 (E_wim v2 (E_wim v1 v1)) (E_wim v1 v1)) (tcd_1 v1 (E_wim v1 v1) v2 (E_wim v2 (E_wim v1 v1)) v0)). Qed.
Lemma tcd_9 (v0 v1 : code_expr) : (template_proof G) (E_wim (E_wim v0 v0) (E_wim v1 (E_wim v0 v0))).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_8 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_10 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v1)) v1) (E_wim v2 v1)).
Proof. exact (TP_mp _ _ (tcd_9 v1 v0) (tcd_0 v1 v1 (E_wim v0 (E_wim v1 v1)) v2)). Qed.
Lemma tcd_11 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v1))) (E_wim v3 (E_wim v2 (E_wim v1 v1)))).
Proof. exact (TP_mp _ _ (tcd_10 v2 v1 v0) (tcd_0 (E_wim v2 (E_wim v1 v1)) v1 (E_wim v0 v1) v3)). Qed.
Lemma tcd_12 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim v2 v2))).
Proof. exact (TP_mp _ _ (tcd_9 v2 v1) (tcd_11 v2 v2 v1 v0)). Qed.
Lemma tcd_13 (v0 v1 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 v1)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_12 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_14 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v0) v1) (E_wim v2 v1)).
Proof. exact (TP_mp _ _ (tcd_13 (E_wim v1 (CEconst 0)) v0) (tcd_0 v1 (CEconst 0) (E_wim v0 v0) v2)). Qed.
Lemma tcd_15 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim v2 v1))).
Proof. exact (TP_mp _ _ (tcd_14 v1 (E_wim v2 v1) v1) (tcd_1 v1 v1 v2 (E_wim v2 v1) v0)). Qed.
Lemma tcd_16 (v0 v1 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 v0)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_15 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_17 (v0 : code_expr) : (template_proof G) (E_wim v0 v0).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_13 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0)). Qed.
Lemma tcd_18 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v0) (E_wim v2 v0)).
Proof. exact (TP_mp _ _ (tcd_17 (E_wim v0 v1)) (tcd_0 v0 v1 (E_wim v0 v1) v2)). Qed.
Lemma tcd_19 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v1 v2)) (E_wim v3 (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_18 v1 v2 v0) (tcd_0 (E_wim v1 v2) v1 (E_wim v0 v1) v3)). Qed.
Lemma tcd_20 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v3 v1)) (E_wim v4 (E_wim v3 v1))).
Proof. exact (TP_mp _ _ (tcd_19 v3 v1 v2 v0) (tcd_0 (E_wim v3 v1) (E_wim v1 v2) (E_wim v0 (E_wim v1 v2)) v4)). Qed.
Lemma tcd_21 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim (E_wim v1 v2) v3) v2) (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_0 v2 (CEconst 0) (E_wim (E_wim v1 v2) v3) v1) (tcd_20 (E_wim v2 (CEconst 0)) (E_wim v1 v2) v3 (E_wim (E_wim (E_wim v1 v2) v3) v2) v0)). Qed.
Lemma tcd_22 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v2) v1) (E_wim v0 v1)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_21 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1 v2)). Qed.
Lemma tcd_23 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim (E_wim v0 v1) v2)) (E_wim v3 (E_wim (E_wim v0 v1) v2))).
Proof. exact (TP_mp _ _ (tcd_22 v0 v1 v2) (tcd_0 (E_wim (E_wim v0 v1) v2) v1 (E_wim v0 v1) v3)). Qed.
Lemma tcd_24 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v1) v1)).
Proof. exact (TP_mp _ _ (tcd_18 v1 v2 (E_wim (E_wim v1 v2) v1)) (tcd_23 (E_wim v1 v2) v1 v1 v0)). Qed.
Lemma tcd_25 (v0 v1 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v0) v0).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_24 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_26 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v0 v1)) (E_wim v2 (E_wim v0 v1))).
Proof. exact (TP_mp _ _ (tcd_25 v0 v1) (tcd_0 (E_wim v0 v1) v0 v0 v2)). Qed.
Lemma tcd_27 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v1 (E_wim v1 v2)) (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_26 v1 v2 (E_wim v1 (E_wim v1 v2))) (tcd_23 v1 (E_wim v1 v2) (E_wim v1 v2) v0)). Qed.
Lemma tcd_28 (v0 v1 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v0 v1)) (E_wim v0 v1)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_27 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1)). Qed.
Lemma tcd_29 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v1 v2)) (E_wim v1 v2)).
Proof. exact (TP_mp _ _ (tcd_19 v0 v1 v2 (E_wim (E_wim v0 v1) (E_wim v1 v2))) (tcd_28 (E_wim (E_wim v0 v1) (E_wim v1 v2)) (E_wim v1 v2))). Qed.
Lemma tcd_30 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v0)) (E_wim v3 (E_wim v2 v0))).
Proof. exact (TP_mp _ _ (tcd_29 v2 v0 v1) (tcd_0 (E_wim v2 v0) (E_wim v0 v1) (E_wim v0 v1) v3)). Qed.
Lemma tcd_31 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim v2 v0))).
Proof. exact (TP_mp _ _ (tcd_30 v0 (E_wim v1 (E_wim v2 v0)) v2 v1) (tcd_22 v0 (E_wim v1 (E_wim v2 v0)) (E_wim v2 v0))). Qed.
Lemma tcd_32 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 (E_wim v2 v3))) v2) (E_wim v4 v2)).
Proof. exact (TP_mp _ _ (tcd_31 (E_wim v2 v3) v0 v1) (tcd_0 v2 v3 (E_wim v0 (E_wim v1 (E_wim v2 v3))) v4)). Qed.
Lemma tcd_33 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 (E_wim v2 v3))) v2) v2).
Proof. exact (TP_mp _ _ (tcd_32 v0 v1 v2 v3 (E_wim (E_wim v0 (E_wim v1 (E_wim v2 v3))) v2)) (tcd_28 (E_wim (E_wim v0 (E_wim v1 (E_wim v2 v3))) v2) v2)). Qed.
Lemma tcd_34 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 (E_wim v2 (E_wim v0 v3)))) (E_wim v4 (E_wim v1 (E_wim v2 (E_wim v0 v3))))).
Proof. exact (TP_mp _ _ (tcd_33 v1 v2 v0 v3) (tcd_0 (E_wim v1 (E_wim v2 (E_wim v0 v3))) v0 v0 v4)). Qed.
Lemma tcd_35 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 (E_wim v2 (E_wim v0 v3)))) (E_wim v1 (E_wim v2 (E_wim v0 v3)))).
Proof. exact (TP_mp _ _ (tcd_34 v0 v1 v2 v3 (E_wim v0 (E_wim v1 (E_wim v2 (E_wim v0 v3))))) (tcd_28 (E_wim v0 (E_wim v1 (E_wim v2 (E_wim v0 v3)))) (E_wim v1 (E_wim v2 (E_wim v0 v3))))). Qed.
Lemma tcd_36 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v1 (E_wim v0 v1))) v2) (E_wim v3 v2)).
Proof. exact (TP_mp _ _ (tcd_2 (E_wim v2 (CEconst 0)) v0 v1) (tcd_0 v2 (CEconst 0) (E_wim (E_wim v0 v1) (E_wim v1 (E_wim v0 v1))) v3)). Qed.
Lemma tcd_37 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v1)) v2) (E_wim v3 v2))).
Proof. exact (TP_mp _ _ (tcd_0 v2 v1 (E_wim v1 (E_wim v2 v1)) v3) (tcd_36 v2 v1 (E_wim (E_wim (E_wim v1 (E_wim v2 v1)) v2) (E_wim v3 v2)) v0)). Qed.
Lemma tcd_38 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v0)) v1) (E_wim v2 v1)) v3) (E_wim v4 v3)).
Proof. exact (TP_mp _ _ (tcd_37 (E_wim v3 (CEconst 0)) v0 v1 v2) (tcd_0 v3 (CEconst 0) (E_wim (E_wim (E_wim v0 (E_wim v1 v0)) v1) (E_wim v2 v1)) v4)). Qed.
Lemma tcd_39 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v1 v2) (E_wim v3 (E_wim v1 v2)))).
Proof. exact (TP_mp _ _ (tcd_38 (CEconst 0) v2 v1 (E_wim v3 (E_wim v1 v2)) (E_wim v1 v2)) (tcd_1 (E_wim (E_wim (CEconst 0) (E_wim v2 (CEconst 0))) v2) (E_wim v1 v2) v3 (E_wim v3 (E_wim v1 v2)) v0)). Qed.
Lemma tcd_40 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v0 v1))).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_39 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1 v2)). Qed.
Lemma tcd_41 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v1) (E_wim v3 v1)).
Proof. exact (TP_mp _ _ (tcd_40 v1 v2 v0) (tcd_0 v1 v2 (E_wim v0 (E_wim v1 v2)) v3)). Qed.
Lemma tcd_42 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v3)) v2) v2)).
Proof. exact (TP_mp _ _ (tcd_41 v1 v2 v3 (E_wim (E_wim v1 (E_wim v2 v3)) v2)) (tcd_23 (E_wim v1 (E_wim v2 v3)) v2 v2 v0)). Qed.
Lemma tcd_43 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v1) v1).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_42 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1 v2)). Qed.
Lemma tcd_44 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 (E_wim v0 v2))) (E_wim v3 (E_wim v1 (E_wim v0 v2)))).
Proof. exact (TP_mp _ _ (tcd_43 v1 v0 v2) (tcd_0 (E_wim v1 (E_wim v0 v2)) v0 v0 v3)). Qed.
Lemma tcd_45 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 (E_wim v0 v2))) (E_wim v1 (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_44 v0 v1 v2 (E_wim v0 (E_wim v1 (E_wim v0 v2)))) (tcd_28 (E_wim v0 (E_wim v1 (E_wim v0 v2))) (E_wim v1 (E_wim v0 v2)))). Qed.
Lemma tcd_46 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v1 v2) (E_wim (E_wim (E_wim v2 v3) v1) v2))).
Proof. exact (TP_mp _ _ (tcd_0 v2 v3 v1 (E_wim (E_wim v2 v3) v1)) (tcd_44 (E_wim (E_wim v2 v3) v1) (E_wim v1 v2) v2 v0)). Qed.
Lemma tcd_47 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim (E_wim v1 v2) v0) v1)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_46 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1 v2)). Qed.
Lemma tcd_48 (v0 v1 v2 v3 v4 v5 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v3 (E_wim v2 v4))) (E_wim v5 (E_wim v3 (E_wim v2 v4)))).
Proof. exact (TP_mp _ _ (tcd_20 v3 v2 v4 v1 v0) (tcd_0 (E_wim v3 (E_wim v2 v4)) (E_wim v1 v2) (E_wim v0 (E_wim v1 v2)) v5)). Qed.
Lemma tcd_49 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v3) (E_wim v2 v3))).
Proof. exact (TP_mp _ _ (tcd_0 v3 (CEconst 0) (E_wim v1 v2) v2) (tcd_48 (E_wim v3 (CEconst 0)) v1 v2 (E_wim (E_wim v1 v2) v3) v3 v0)). Qed.
Lemma tcd_50 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v1 v2)).
Proof. exact (TP_mp _ _ (tcd_0 (CEconst 0) (CEconst 0) (CEconst 0) (CEconst 0)) (tcd_49 (E_wim (E_wim (E_wim (CEconst 0) (CEconst 0)) (CEconst 0)) (E_wim (E_wim (CEconst 0) (CEconst 0)) (E_wim (CEconst 0) (CEconst 0)))) v0 v1 v2)). Qed.
Lemma tcd_51 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v0 v1) (E_wim v2 v1))).
Proof. exact (TP_mp _ _ (tcd_0 v1 (CEconst 0) v0 v2) (tcd_50 (E_wim v1 (CEconst 0)) v0 (E_wim (E_wim v0 v1) (E_wim v2 v1)))). Qed.
Lemma tcd_52 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3) v0) (E_wim (E_wim v0 v1) (E_wim v2 v1))).
Proof. exact (TP_mp _ _ (tcd_51 v0 v1 v2) (tcd_47 v0 (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3)). Qed.
Lemma tcd_53 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim (E_wim v1 v3) v1)) (E_wim v0 v1)).
Proof. exact (TP_mp _ _ (tcd_18 v1 v3 v0) (tcd_47 (E_wim (E_wim v1 v3) v1) (E_wim v0 v1) v2)). Qed.
Lemma tcd_54 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim (E_wim v3 (E_wim v1 v4)) v1)) (E_wim v0 v1)).
Proof. exact (TP_mp _ _ (tcd_41 v3 v1 v4 v0) (tcd_47 (E_wim (E_wim v3 (E_wim v1 v4)) v1) (E_wim v0 v1) v2)). Qed.
Lemma tcd_55 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v3 v2)) v0) (E_wim v4 v0)).
Proof. exact (TP_mp _ _ (tcd_51 (E_wim v0 v1) v2 v3) (tcd_0 v0 v1 (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v3 v2)) v4)). Qed.
Lemma tcd_56 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v3 v2)) v0) v0).
Proof. exact (TP_mp _ _ (tcd_55 v0 v1 v2 v3 (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v3 v2)) v0)) (tcd_28 (E_wim (E_wim (E_wim (E_wim v0 v1) v2) (E_wim v3 v2)) v0) v0)). Qed.
Lemma tcd_57 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 (E_wim (E_wim v1 v2) v3)) (E_wim v1 v2)) v4) v2) (E_wim v1 v2)).
Proof. exact (TP_mp _ _ (tcd_56 (E_wim (E_wim v0 (E_wim (E_wim v1 v2) v3)) (E_wim v1 v2)) v4 v2 v1) (tcd_54 (E_wim (E_wim (E_wim (E_wim v0 (E_wim (E_wim v1 v2) v3)) (E_wim v1 v2)) v4) v2) (E_wim v1 v2) (E_wim (E_wim v0 (E_wim (E_wim v1 v2) v3)) (E_wim v1 v2)) v0 v3)). Qed.
Lemma tcd_58 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v1) v3)) (E_wim (E_wim v1 v2) v1)) v1).
Proof. exact (TP_mp _ _ (tcd_57 v0 (E_wim v1 v2) v1 v3 v1) (tcd_53 (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v1) v3)) (E_wim (E_wim v1 v2) v1)) v1 v1 v2)). Qed.
Lemma tcd_59 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim (E_wim v0 v2) v0) v1)).
Proof. exact (TP_mp _ _ (tcd_58 (E_wim v0 v1) v0 v2 v1) (tcd_52 v0 v1 (E_wim (E_wim v0 v2) v0) (E_wim (E_wim v0 v2) v0))). Qed.
Lemma tcd_60 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) (E_wim v1 (E_wim v1 v2))) (E_wim v0 (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_26 v1 v2 v0) (tcd_47 (E_wim v1 (E_wim v1 v2)) (E_wim v0 (E_wim v1 v2)) v3)). Qed.
Lemma tcd_61 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v0) (E_wim (E_wim v0 v2) (E_wim v3 v2))).
Proof. exact (TP_mp _ _ (tcd_51 v0 v2 v3) (tcd_59 v0 (E_wim (E_wim v0 v2) (E_wim v3 v2)) v1)). Qed.
Lemma tcd_62 (v0 v1 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v0 v1) v1)).
Proof. exact (TP_mp _ _ (tcd_61 v0 (E_wim (E_wim v0 v1) v1) v1 (E_wim v0 v1)) (tcd_60 v0 (E_wim v0 v1) v1 v0)). Qed.
Lemma tcd_63 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v0) (E_wim (E_wim v0 v2) v2)).
Proof. exact (TP_mp _ _ (tcd_62 v0 v2) (tcd_59 v0 (E_wim (E_wim v0 v2) v2) v1)). Qed.
Lemma tcd_64 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v1) (E_wim v0 v2)) (E_wim v3 (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_63 v0 v2 v1) (tcd_0 (E_wim v0 v2) v0 (E_wim (E_wim v0 v1) v1) v3)). Qed.
Lemma tcd_65 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v1) (E_wim v0 v2)) (E_wim v0 v2)).
Proof. exact (TP_mp _ _ (tcd_64 v0 v1 v2 (E_wim (E_wim (E_wim v0 v1) v1) (E_wim v0 v2))) (tcd_28 (E_wim (E_wim (E_wim v0 v1) v1) (E_wim v0 v2)) (E_wim v0 v2))). Qed.
Lemma tcd_66 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v2) (E_wim v0 (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_31 v2 v0 v1) (tcd_47 v2 (E_wim v0 (E_wim v1 v2)) v3)). Qed.
Lemma tcd_67 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim (E_wim v0 v2) (E_wim v3 v2)))).
Proof. exact (TP_mp _ _ (tcd_61 v0 (E_wim v1 (E_wim (E_wim v0 v2) (E_wim v3 v2))) v2 v3) (tcd_66 v0 v1 (E_wim (E_wim v0 v2) (E_wim v3 v2)) v0)). Qed.
Lemma tcd_68 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim (E_wim v0 v1) v1) v2) (E_wim v3 v2))).
Proof. exact (TP_mp _ _ (tcd_67 (E_wim (E_wim v0 v1) v1) v0 v2 v3) (tcd_65 v0 v1 (E_wim (E_wim (E_wim (E_wim v0 v1) v1) v2) (E_wim v3 v2)))). Qed.
Lemma tcd_69 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) v1) v2) (E_wim v0 v2)).
Proof. exact (TP_mp _ _ (tcd_68 v0 v1 v2 v0) (tcd_45 v0 (E_wim (E_wim (E_wim v0 v1) v1) v2) v2)). Qed.
Lemma tcd_70 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v3))) (E_wim v4 (E_wim v2 (E_wim v1 v3)))).
Proof. exact (TP_mp _ _ (tcd_41 v2 v1 v3 v0) (tcd_0 (E_wim v2 (E_wim v1 v3)) v1 (E_wim v0 v1) v4)). Qed.
Lemma tcd_71 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v3))) (E_wim v2 (E_wim v1 v3))).
Proof. exact (TP_mp _ _ (tcd_70 v0 v1 v2 v3 (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v3)))) (tcd_28 (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v1 v3))) (E_wim v2 (E_wim v1 v3)))). Qed.
Lemma tcd_72 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim (E_wim (E_wim v2 v0) v3) (E_wim v4 v3)))).
Proof. exact (TP_mp _ _ (tcd_67 (E_wim v2 v0) v1 v3 v4) (tcd_50 v2 v0 (E_wim v1 (E_wim (E_wim (E_wim v2 v0) v3) (E_wim v4 v3))))). Qed.
Lemma tcd_73 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim (E_wim v0 v2) v2)) v3) (E_wim v4 v3))).
Proof. exact (TP_mp _ _ (tcd_72 (E_wim (E_wim v0 v2) v2) v0 v1 v3 v4) (tcd_65 v0 v2 (E_wim (E_wim (E_wim v1 (E_wim (E_wim v0 v2) v2)) v3) (E_wim v4 v3)))). Qed.
Lemma tcd_74 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v3) v3)) v4) (E_wim v2 v4)).
Proof. exact (TP_mp _ _ (tcd_73 (E_wim v1 v2) v0 v3 v4 v2) (tcd_71 v1 v2 (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v3) v3)) v4) v4)). Qed.
Lemma tcd_75 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) v2) (E_wim (E_wim (E_wim v3 v0) v2) v2)).
Proof. exact (TP_mp _ _ (tcd_74 (E_wim (E_wim v0 v1) v2) v3 v0 v2 v1) (tcd_52 (E_wim v0 v1) v2 (E_wim (E_wim v3 v0) v2) v1)). Qed.
Lemma tcd_76 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 v1) v1) v2) v0) (E_wim (E_wim v0 v1) v1)).
Proof. exact (TP_mp _ _ (tcd_62 v0 v1) (tcd_47 v0 (E_wim (E_wim v0 v1) v1) v2)). Qed.
Lemma tcd_77 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v0)) (E_wim v2 v0)).
Proof. exact (TP_mp _ _ (tcd_30 v0 v1 v2 (E_wim (E_wim v0 v1) (E_wim v2 v0))) (tcd_28 (E_wim (E_wim v0 v1) (E_wim v2 v0)) (E_wim v2 v0))). Qed.
Lemma tcd_78 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim (E_wim v0 v2) v2))).
Proof. exact (TP_mp _ _ (tcd_63 v0 (E_wim v1 (E_wim (E_wim v0 v2) v2)) v2) (tcd_66 v0 v1 (E_wim (E_wim v0 v2) v2) v0)). Qed.
Lemma tcd_79 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim v1 (E_wim (E_wim (E_wim v2 v0) v3) v3))).
Proof. exact (TP_mp _ _ (tcd_78 (E_wim v2 v0) v1 v3) (tcd_50 v2 v0 (E_wim v1 (E_wim (E_wim (E_wim v2 v0) v3) v3)))). Qed.
Lemma tcd_80 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim (E_wim v0 v2) v2)) v3) v3)).
Proof. exact (TP_mp _ _ (tcd_79 (E_wim (E_wim v0 v2) v2) v0 v1 v3) (tcd_65 v0 v2 (E_wim (E_wim (E_wim v1 (E_wim (E_wim v0 v2) v2)) v3) v3))). Qed.
Lemma tcd_81 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v3) v3)) v1) v1).
Proof. exact (TP_mp _ _ (tcd_80 (E_wim v1 v2) v0 v3 v1) (tcd_77 v1 v2 (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 v2) v3) v3)) v1))). Qed.
Lemma tcd_82 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim (E_wim (E_wim v0 v1) v2) v2)) (E_wim (E_wim (E_wim v0 v1) v2) v2)).
Proof. exact (TP_mp _ _ (tcd_81 (E_wim v0 (E_wim (E_wim (E_wim v0 v1) v2) v2)) v0 v1 v2) (tcd_76 v0 (E_wim (E_wim (E_wim v0 v1) v2) v2) v0)). Qed.
Lemma tcd_83 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v3 v1)) (E_wim v3 v1)).
Proof. exact (TP_mp _ _ (tcd_20 v0 v1 v2 v3 (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v3 v1))) (tcd_28 (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v3 v1)) (E_wim v3 v1))). Qed.
Lemma tcd_84 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v3)) v4) v4)) v2) v2).
Proof. exact (TP_mp _ _ (tcd_80 (E_wim v1 (E_wim v2 v3)) v0 v4 v2) (tcd_83 v1 v2 v3 (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v3)) v4) v4)) v2))). Qed.
Lemma tcd_85 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim (E_wim v2 (E_wim v0 v3)) v1) v1)).
Proof. exact (TP_mp _ _ (tcd_84 (E_wim v0 v1) v2 v0 v3 v1) (tcd_52 v0 v1 (E_wim (E_wim v2 (E_wim v0 v3)) v1) v0)). Qed.
Lemma tcd_86 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v0 v2)) v1) v1).
Proof. exact (TP_mp _ _ (tcd_85 v0 v1 (E_wim v0 v1) v2) (tcd_82 (E_wim v0 v1) (E_wim v0 v2) v1)). Qed.
Lemma tcd_87 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim v1 v2) (E_wim v1 v3))) v2) v2).
Proof. exact (TP_mp _ _ (tcd_86 v1 v2 v3) (tcd_75 (E_wim (E_wim v1 v2) (E_wim v1 v3)) v2 v2 v0)). Qed.
Lemma tcd_88 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim (E_wim v1 v0) (E_wim v1 v2))).
Proof. exact (TP_mp _ _ (tcd_87 (E_wim v0 (E_wim v1 v2)) v1 v0 v2) (tcd_52 v0 (E_wim v1 v2) (E_wim v1 v0) v0)). Qed.
Lemma tcd_89 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim v0 (E_wim (E_wim v1 v2) (E_wim v3 v2)))).
Proof. exact (TP_mp _ _ (tcd_67 v1 v0 v2 v3) (tcd_88 v1 v0 (E_wim (E_wim v1 v2) (E_wim v3 v2)))). Qed.
Lemma tcd_90 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v0 v1) (E_wim (E_wim v1 v2) (E_wim v3 v2)))).
Proof. exact (TP_mp _ _ (tcd_89 (E_wim v0 v1) v1 v2 v3) (tcd_69 v0 v1 (E_wim (E_wim v0 v1) (E_wim (E_wim v1 v2) (E_wim v3 v2))))). Qed.
Lemma tcd_91 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim v1 v2) (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_90 v0 v1 v2 v0) (tcd_35 v0 (E_wim v0 v1) (E_wim v1 v2) v2)). Qed.
Lemma tcd_92 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim (E_wim v1 v0) v2) v2)).
Proof. exact (TP_mp _ _ (tcd_62 (E_wim v1 v0) v2) (tcd_50 v1 v0 (E_wim (E_wim (E_wim v1 v0) v2) v2))). Qed.
Lemma tcd_93 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v3) v1) (E_wim v4 v1)).
Proof. exact (TP_mp _ _ (tcd_92 (E_wim v1 v2) v0 v3) (tcd_0 v1 v2 (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v3) v4)). Qed.
Lemma tcd_94 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v3) v1) v1).
Proof. exact (TP_mp _ _ (tcd_93 v0 v1 v2 v3 (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v3) v1)) (tcd_28 (E_wim (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v3) v3) v1) v1)). Qed.
Lemma tcd_95 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v3)) v2) v4)) v2) v2).
Proof. exact (TP_mp _ _ (tcd_94 v0 (E_wim (E_wim v1 (E_wim v2 v3)) v2) v4 v2) (tcd_54 (E_wim (E_wim v0 (E_wim (E_wim (E_wim v1 (E_wim v2 v3)) v2) v4)) v2) v2 (E_wim (E_wim v1 (E_wim v2 v3)) v2) v1 v3)). Qed.
Lemma tcd_96 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim (E_wim v2 (E_wim v0 v3)) v0) v1)).
Proof. exact (TP_mp _ _ (tcd_95 (E_wim v0 v1) v2 v0 v3 v1) (tcd_52 v0 v1 (E_wim (E_wim v2 (E_wim v0 v3)) v0) v0)). Qed.
Lemma tcd_97 (v0 v1 v2 v3 v4 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim v0 (E_wim v1 v2)) v1) (E_wim (E_wim v1 v3) (E_wim v4 v3))).
Proof. exact (TP_mp _ _ (tcd_51 v1 v3 v4) (tcd_96 v1 (E_wim (E_wim v1 v3) (E_wim v4 v3)) v0 v2)). Qed.
Lemma tcd_98 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3) (E_wim v0 v3)).
Proof. exact (TP_mp _ _ (tcd_97 (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3) v0 v3 v1 v2) (tcd_52 (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3 v0 v0)). Qed.
Lemma tcd_99 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim v0 (E_wim v2 v1))).
Proof. exact (TP_mp _ _ (tcd_69 v0 v1 (E_wim v2 v1)) (tcd_98 (E_wim v0 v1) v1 v2 (E_wim v0 (E_wim v2 v1)))). Qed.
Lemma tcd_100 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim v2 (E_wim v0 (E_wim v3 v1)))).
Proof. exact (TP_mp _ _ (tcd_99 v0 v1 v3) (tcd_99 (E_wim v0 v1) (E_wim v0 (E_wim v3 v1)) v2)). Qed.
Lemma tcd_101 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v0 (E_wim v1 (E_wim v3 v2)))).
Proof. exact (TP_mp _ _ (tcd_100 v1 v2 v0 v3) (tcd_88 (E_wim v1 v2) v0 (E_wim v1 (E_wim v3 v2)))). Qed.
Lemma tcd_102 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim v0 (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v1 (E_wim v3 v2)))).
Proof. exact (TP_mp _ _ (tcd_101 (E_wim v0 (E_wim v1 v2)) v1 v2 v3) (tcd_69 v0 (E_wim v1 v2) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v1 (E_wim v3 v2))))). Qed.
Lemma tcd_103 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v1 (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_102 v0 v1 v2 v0) (tcd_35 v0 (E_wim v0 (E_wim v1 v2)) v1 v2)). Qed.
Lemma tcd_104 (v0 v1 v2 v3 : code_expr) : (template_proof G) (E_wim (E_wim (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3) (E_wim (E_wim v2 v0) v3)).
Proof. exact (TP_mp _ _ (tcd_91 v2 v0 v1) (tcd_91 (E_wim v2 v0) (E_wim (E_wim v0 v1) (E_wim v2 v1)) v3)). Qed.
Lemma tcd_105 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 v1) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_88 (E_wim v1 v2) v0 v2) (tcd_104 v1 v2 v0 (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim v0 v2)))). Qed.
Lemma tcd_106 (v0 v1 v2 : code_expr) : (template_proof G) (E_wim (E_wim v0 (E_wim v1 v2)) (E_wim (E_wim v0 v1) (E_wim v0 v2))).
Proof. exact (TP_mp _ _ (tcd_105 v0 v1 v2) (tcd_103 (E_wim v0 v1) (E_wim v0 (E_wim v1 v2)) (E_wim v0 v2))). Qed.

Lemma template_K (p q : code_expr) : (template_proof G) (E_wim p (E_wim q p)).
Proof. exact (tcd_16 p q). Qed.
Lemma template_P (p q : code_expr) : (template_proof G) (E_wim (E_wim (E_wim p q) p) p).
Proof. exact (tcd_25 p q). Qed.
Lemma template_B (p q r : code_expr) : (template_proof G) (E_wim (E_wim p q) (E_wim (E_wim q r) (E_wim p r))).
Proof. exact (tcd_91 p q r). Qed.
Lemma template_S (p q r : code_expr) : (template_proof G) (E_wim (E_wim p (E_wim q r)) (E_wim (E_wim p q) (E_wim p r))).
Proof. exact (tcd_106 p q r). Qed.

End Templates.

Arguments template_K {G} p q.
Arguments template_P {G} p q.
Arguments template_B {G} p q r.
Arguments template_S {G} p q r.

Print Assumptions template_K.
Print Assumptions template_P.
Print Assumptions template_B.
Print Assumptions template_S.
