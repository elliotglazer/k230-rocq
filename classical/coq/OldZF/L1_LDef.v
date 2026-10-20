(** * L1_LDef: pure-logic provability [lprov] = [prov] without the ZF axioms (EXT REP POW UNI INF).
    Used to show that variant axiom texts are interderivable with the originals using logic only. *)
From OldZF Require Import Logic.

Inductive lprov : wff -> Prop :=
  | LDET a b : lprov (Wim a b) -> lprov a -> lprov b
  | LGEN x a : lprov a -> lprov (Wal x a)
  | LB1 a b c : lprov (Wim (Wim a b) (Wim (Wim b c) (Wim a c)))
  | LB2 a : lprov (Wim (Wim (Wn a) a) a)
  | LB3 a b : lprov (Wim a (Wim (Wn a) b))
  | LB4 x a b : lprov (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b)))
  | LB6a x y z : x <> z -> y <> z ->
      lprov (Wa (Wim (Weq x y) (Wal z (Weq x y))) (Wim (Wel x y) (Wal z (Wel x y))))
  | LB6b x y a : lprov (Wim (Wal x (Wal y a)) (Wal y (Wal x a)))
  | LB6c x a : lprov (Wim (Wex x (Wal x a)) a)
  | LB7 x y : lprov (Wex x (Weq x y))
  | LB8a x y z : lprov (Wim (Weq x y) (Wim (Weq x z) (Weq y z)))
  | LB8b x y z : lprov (Wim (Weq x y) (Wim (Wel x z) (Wel y z)))
  | LB8c x y z : lprov (Wim (Weq x y) (Wim (Wel z x) (Wel z y))).

Lemma lprov_prov a : lprov a -> prov a.
Proof.
  induction 1; try (econstructor; eassumption); try now constructor.
Qed.
