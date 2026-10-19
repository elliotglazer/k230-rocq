(** Adapted from the pinned m254/Enum254.v; same command calculus with K230 bundle. *)
(** * Enum230: the abstract proof enumerator = one run of main() of zf/m230/inputs/source.py.

    INTERFACE FILE (frozen 2026-10-13): the program layer proves that one run of the program root
    from a boundary state (scratch1 = scratch2 = axiomcode = 0) is [enum_step]; L1 proves
    [enum230_halts <-> thm230 1].  Validated against the register-machine semantics of the compiled
    source in zf/m230/logic/validate.py (spec.py is the same function).

    Persistent registers at a command boundary:
      pl = prooflist, np = nextproof, tw = topwff, ws = wffstack (stream P top rest; 0 = zeros),
      d = param1 (additive parameter counter), h = param2 (the cached formula).
    Commands (selector, then fields read from the command list):
      0       MP    x        : d += x; if wim tw d = h then tw := d and push 0, else tw := 0; h := 0
      1       DROP  x        : d += x; push tw; tw := h
      2       NIP   x        : d += x; if h = 1 then HALT else h := pop
      3 + c   AX    x y u    : d += x; a := d; b := h + y; push tw, wal a h, rho8 .. rho1;
                               tw := (if c = a or c = b then 0 else bundle a b c); d := 0; h := 0
    The first command of a candidate is read from the candidate number itself (prooflist was 0 and
    is loaded with nextproof, which is incremented); later commands are read from prooflist - 1. *)
From Coq Require Import Arith Lia Bool.
From K230L Require Import Codes230.

Record state : Type := mkState { pl : nat; np : nat; tw : nat; ws : nat; d : nat; h : nat }.

Definition s0 : state := mkState 0 0 0 0 0 0.

(** the stack after AX: [tw] pushed first, then GEN of the cache, then rho8 .. rho1 *)
Definition ax_stack (a h b c u t w : nat) : nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (rho7 a b c) (P (rho8 a b c u) (P (wal a h) (P t w))))))))).

Definition gate (a b c : nat) : nat := if Nat.eqb c a || Nat.eqb c b then 0 else bundle a b c.

Definition enum_step (s : state) : option state :=
  let '(pl1, np1) := if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s) in
  let '(ac, pl2) := unP pl1 in
  let '(x, pl3) := unP pl2 in
  let d1 := d s + x in
  match ac with
  | 0 => Some (if Nat.eqb (wim (tw s) d1) (h s)
               then mkState pl3 np1 d1 (P 0 (ws s)) d1 0
               else mkState pl3 np1 0 (ws s) d1 0)
  | 1 => Some (mkState pl3 np1 (h s) (P (tw s) (ws s)) d1 (h s))
  | 2 => if Nat.eqb (h s) 1 then None
         else let '(h1, w1) := unP (ws s) in Some (mkState pl3 np1 (tw s) w1 d1 h1)
  | S (S (S c)) =>
      let '(y, pl4) := unP pl3 in
      let '(u, pl5) := unP pl4 in
      let b := h s + y in
      Some (mkState pl5 np1 (gate d1 b c) (ax_stack d1 (h s) b c u (tw s) (ws s)) 0 0)
  end.

(** [run n s]: n steps from s, [None] if a step halts on the way *)
Fixpoint run (n : nat) (s : state) : option state :=
  match n with
  | 0 => Some s
  | S n => match enum_step s with Some s' => run n s' | None => None end
  end.

(** The machine halts iff some reachable state makes a halting step (a NIP with cache 1). *)
Definition enum230_halts : Prop := exists n s, run n s0 = Some s /\ enum_step s = None.
