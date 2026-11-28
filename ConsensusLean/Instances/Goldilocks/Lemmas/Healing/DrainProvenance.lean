module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.WidthVocab
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: stored slow-lock provenance

Every lock that is not fast and that an honest node holds sits below (inside `U`) the **stored**
block `Φ.viableAncestor D` of a slow lock of its slot that the node itself wrote at an earlier cut
(`D` the slow selection of `SlowLockAt`, `Φ` the frame of the writing call): `add_locks` stores
exactly that block (`liveLocks` moves the new lock to its viable ancestor), the lock functions
only move locks back and keep their slot and fast bit (A0.4 (c)), a restart keeps the locks
(A0.7), an optimistic confirmation writes only fast locks, and an update writes a lock that is
not fast only as its slow lock. This is the slow case of the induction of `fast_lock_provenance`
(`AC/Steps/Provenance`), read through the `FromP` lemmas of its writing functions there
(`FromP.of_onTick`, `FromP.of_tryVote`, `FromP.of_optimistic`) and the shared `FromP` toolkit
(`Lemmas/AC/LockProvenance`), with the stored block of HR.4's
`stored_fast_lock_provenance` (`Retention/Provenance`)
(every lock image retains its original label).
`slow_lock_provenance` (`AC/SlowLock`) is its corollary for the raw selection `D`. Over a run at a
write mode `wm` the slow lock has width `wm.width` (`slow_lock_provenance_storedM`, `SlowLockAtW`).
-/

namespace Consensus.Goldilocks.AC

variable {wm : AC.WriteMode}

variable {FGP : Type} {sp : ACParams}

variable {U : Set (Blk sp.n FGP)}

variable {H : Set (Fin sp.n)} {tr : GTrace sp FGP}

/-- A call of an honest node keeps its locks below earlier ones, or writes fast locks, or writes
a slow lock of width `wm.width` of the slot of its update. -/
private theorem call_fromPU
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = false →
        ∃ D, SlowLockAtW wm.width tr x i s D ∧ O = ℓ.frame.viableAncestor D) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hU := hr.coherent
  have fast : ∀ s (f : Bool) (O : Blk sp.n FGP), f = true → f = false →
      ∃ D, SlowLockAtW wm.width tr x i s D ∧ O = ℓ.frame.viableAncestor D :=
    fun _ _ _ h1 h2 => absurd (h1.symm.trans h2) (by simp)
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  simp only at hpost
  rw [← hpost]
  have hlaw := hr.lawfulAt hx hc hΦ
  generalize hA : tr.state x i = A at hpost hlaw
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hlaw
    refine (FromP.of_onTick (wm := wm) (L := u i) hU hΦ hΦU x A _ hlaw).mono
      fun s f B h hf => ?_
    obtain ⟨D, -, rfl, ⟨-, -, h, -⟩ | ⟨ht, hs0, hj, hs, -, -, hW⟩⟩ := h
    · exact fast s f _ h hf
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [ACParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      obtain ⟨C, h1, h2⟩ := hW hf
      exact ⟨D, slowLockAtW_iff.2 ⟨ℓ, C, hu, hA ▸ h1, hA ▸ h2⟩, rfl⟩
  | proposal => exact FromP.of_eq rfl
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    rw [hcall] at hlaw
    have h₁ := FromP.of_optimistic_admit hU hΦ hΦU A rfl (tr.time i) m
    exact (FromP.trans hU (h₁.mono fun _ _ _ ⟨_, _, _, h, _⟩ => h)
      ((FromP.of_tryVote (wm := wm) (L := u i) hU hΦ hΦU x _ _ hlaw).mono
        fun _ _ _ ⟨_, _, _, _, _, h, _⟩ => h)).mono fun s f B h hf => fast s f B h hf
  | block B =>
    rw [hcall] at hlaw
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B)
        (tr.time i)
    rw [blockReceipt_locks] at h₁
    exact (FromP.trans hU (h₁.mono fun _ _ _ ⟨_, _, _, h, _⟩ => h)
      ((FromP.of_tryVote (wm := wm) (L := u i) hU hΦ hΦU x _ _ hlaw).mono
        fun _ _ _ ⟨_, _, _, _, _, h, _⟩ => h)).mono fun s f B h hf => fast s f B h hf
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

/-- **Stored slow-lock provenance at width `wm.width`**: every lock that is not fast and that an
honest node holds before cut `i` sits below (inside `U`) the stored block
`ℓ.frame.viableAncestor D` of a slow lock of width `wm.width` of its slot (selection `D`) that the
node wrote at an earlier cut `j` (call label `ℓ`). -/
theorem slow_lock_provenance_storedM
    {u : Nat → Set Lock} {ini} (hr : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ j < i, ∃ ℓ D, tr.CallAt x j ℓ ∧ SlowLockAtW wm.width tr x j l.slot D ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L (ℓ.frame.viableAncestor D) := by
  induction i with
  | zero =>
    intro l hl
    change l ∈ (tr.init x).locks at hl
    obtain ⟨m, hm⟩ := AC.voteStart_iff.1 (hini x)
    rw [hr.init x hx, hm] at hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    intro l hl hf
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      rcases fromP_iff.1 (call_fromPU hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨O, h, hB⟩
      · obtain ⟨j, hj, ℓ', D, hc, h, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hs ▸ h,
          below_iff.1 (Below.of_sitsBelow hr.coherent hb (below_iff.2 hB))⟩
      · obtain ⟨D, hD, rfl⟩ := h hf
        exact ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, below_iff.1 hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl hf
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

end Consensus.Goldilocks.AC

end
