module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkFacts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: stored fast-lock provenance

`AC.fast_lock_provenance` places every fast lock below the **raw** selection `D` of a fast-lock
write; HR.4's attestations need the **stored** block `O = Φ.viableAncestor D` of that write (`Φ` the
frame of the writing call), since `Q ⪯ D` and `O ⪯ D` do not give `Q ⪯ O`.
`stored_fast_lock_provenance` keeps `O`: `add_locks` stores exactly `O` (`liveLocks` moves the new
lock to its viable ancestor), the lock functions only move locks back (A0.4 (c)), a restart keeps
the locks (A0.7), and every insertion is an optimistic check or the fast test of an update, in
the frame of the call that runs it. The writing functions are read through the `FromP` lemmas of
`AC/Steps/Provenance` at the parent's write mode. A fast-lock write is joined
(`joined_of_fastLockAt`): the update's guard, or the optimistic check's guard at a substep that
keeps `restart_time`. -/

namespace Consensus.Goldilocks.Healing

open AC

variable {FGP : Type} {sp : ACParams}

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

private theorem FromP.of_proposal (A : ACState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop} :
    FromP U A.locks (acProposal sp A Φ t).1.locks New := by
  unfold acProposal
  split_ifs <;> exact FromP.of_eq rfl

/-! ## Over an AC trace -/

variable {H : Set (Fin sp.n)} {tr : GTrace sp FGP}
  {ini : Fin sp.n → ACState sp.n}

/-- A call of an honest node keeps its locks below earlier ones or writes fast locks stored on
the viable ancestor (in the call's frame) of a fast-lock write's selection at its own cut. -/
private theorem call_storedFrom (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = true → ∃ CV ℓ' D, tr.CallAt x i ℓ' ∧ FastLockAt tr x i s D CV ∧
        O = ℓ'.frame.viableAncestor D) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hU := hr.coherent
  have opt : ∀ s (f : Bool) D, (∃ CV, OptimisticLockAt tr x i s D CV) →
      f = true → ∃ CV ℓ' D', tr.CallAt x i ℓ' ∧ FastLockAt tr x i s D' CV ∧
        ℓ.frame.viableAncestor D = ℓ'.frame.viableAncestor D' :=
    fun s f D ⟨CV, h⟩ _ => ⟨CV, ℓ, D, hc, Or.inr h, rfl⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (FromP.of_onTick (wm := AC.WriteMode.parent sp) hU hΦ hΦU x A (tr.time i)
      (unlockRel_unlock hΦ _ _ _ _)).mono fun s f O h => ?_
    obtain ⟨D, -, rfl, ⟨e, he', -, hs, hsel⟩ | ⟨ht, hs0, hj, hs, hC, -, -⟩⟩ := h
    · exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [ACParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      intro hf
      obtain ⟨C₀, hC₀, hD₀⟩ := hC hf
      exact ⟨_, ℓ, D, hc, Or.inl ⟨ℓ, C₀, hu, hA ▸ hC₀, hA ▸ hD₀, rfl⟩, rfl⟩
  | proposal => exact FromP.of_proposal A _
  | toFG => exact FromP.of_eq (AC.toFG_locks A _)
  | message m =>
    rw [hcall] at hemits
    refine FromP.trans hU ((FromP.of_optimistic_admit hU hΦ hΦU A rfl _ m).mono
      fun s f O h => ?_) ((FromP.of_tryVote (wm := AC.WriteMode.parent sp) hU hΦ hΦU x
        (optimisticConfirmation sp (admitVote sp A (tr.time i) m) ℓ.frame (tr.time i))
        (tr.time i)
        (unlockRel_unlock hΦ _ _ _ _)).mono fun s f O h => ?_)
    · obtain ⟨D, -, rfl, -, hs, hsel⟩ := h
      exact opt _ _ D ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, hs.symm, hsel, rfl⟩
    · obtain ⟨D, -, rfl, e, he', -, hs, hsel⟩ := h
      exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    refine FromP.trans hU (h₁.mono fun s f O h => ?_)
      ((FromP.of_tryVote (wm := AC.WriteMode.parent sp) hU hΦ hΦU x
        (optimisticConfirmation sp (blockReceipt sp A (tr.time i) B) ℓ.frame (tr.time i))
        (tr.time i)
        (unlockRel_unlock hΦ _ _ _ _)).mono fun s f O h => ?_)
    · obtain ⟨D, -, rfl, -, hs, hsel⟩ := h
      exact opt _ _ D ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, hs.symm, hsel, rfl⟩
    · obtain ⟨D, -, rfl, e, he', -, hs, hsel⟩ := h
      exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

/-- **Stored fast-lock provenance.** Every fast lock that an honest node holds before cut `i`
sits below (inside `U`) the stored block `O = Φ.viableAncestor D` of a fast-lock write of its
slot at an earlier cut of the node, `D` the write's selection and `Φ` the frame of its call. -/
theorem stored_fast_lock_provenance (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    (hini : ∀ y, AC.VoteStart sp.genesisRoot (ini y))
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ r < i, ∃ CV ℓ D, tr.CallAt x r ℓ ∧ FastLockAt tr x r l.slot D CV ∧
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
      rcases fromP_iff.1 (call_storedFrom hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨O, h, hB⟩
      · obtain ⟨r, hri, CV, ℓ', D, hc, hfl, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨r, hri.trans (Nat.lt_succ_self i), CV, ℓ', D, hc, hs ▸ hfl,
          AC.below_iff.1 (AC.Below.of_sitsBelow hr.coherent hb (AC.below_iff.2 hB))⟩
      · obtain ⟨CV, ℓ', D, hc, hfl, rfl⟩ := h hf
        exact ⟨i, Nat.lt_succ_self i, CV, ℓ', D, hc, hfl, AC.below_iff.1 hB⟩
    · obtain ⟨r, hri, h⟩ := ih l hl hf
      exact ⟨r, hri.trans (Nat.lt_succ_self i), h⟩

/-! ## The joined guard of a write -/

/-- **A fast-lock write is joined**: its call is not a restart, and the state before it is
joined at its time (the update's guard; the optimistic check's guard at a substep that keeps
`restart_time`). -/
theorem joined_of_fastLockAt (hr : ACLocalRun (goldilocksAC sp FGP) H U tr ini) {x : Fin sp.n}
    (hx : x ∈ H) {i s : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (h : FastLockAt tr x i s D CV) :
    joined sp (tr.state x i) (tr.time i) ∧
      ∃ ℓ, tr.CallAt x i ℓ ∧ ℓ.call ≠ .restart := by
  rcases h with ⟨ℓ, C, ⟨hc, htick, -, hj⟩, -⟩ | ⟨ℓ, A, ⟨hc, hA⟩, -, hsel, -⟩
  · exact ⟨hj, ℓ, hc, by rw [htick]; exact fun h => nomatch h⟩
  have hjA : joined sp A (tr.time i) := by
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with h1
    exact not_not.mp (not_or.mp h1).1
  have hrs : ∀ A' : ACState sp.n, A'.restartTime = (tr.state x i).restartTime →
      joined sp A' (tr.time i) → joined sp (tr.state x i) (tr.time i) := by
    intro A' h hj
    unfold joined at hj ⊢
    rwa [← h]
  rcases hA with ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩ | ⟨e, he, rfl⟩
  · exact ⟨hrs _ (AC.admitVote_restartTime _ _ _) hjA, ℓ, hc, by rw [hm]; exact fun h => nomatch h⟩
  · exact ⟨hrs _ (blockReceipt_restartTime _ _ _) hjA, ℓ, hc,
      by rw [hB]; exact fun h => nomatch h⟩
  · have hnr : ℓ.call ≠ .restart := by
      intro hres
      have hexec := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
      rw [hres] at hexec
      obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hx hc
      have h0 := ((restart_state sp) FGP (tr.node i) (tr.state (tr.node i) i) ℓ.frame
        (tr.time i) hΦ (hr.time_nonneg i)).1
      rw [show ℓ.emits = [] from (congrArg Prod.snd hexec).symm.trans h0] at he
      exact absurd he List.not_mem_nil
    have hexec := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1] at hexec
    have hpr : (tr.post i).restartTime = (tr.state x i).restartTime := by
      have h1 := congrArg Prod.fst hexec
      simp only at h1
      rw [← h1]
      exact step_restartTime x _ _ _ _ hnr
    have := restartTime_of_castAtU hr.toU hx ⟨hc, he⟩
    exact ⟨hrs _ ((AC.admitVote_restartTime _ _ _).trans (this.symm.trans hpr)) hjA, ℓ, hc, hnr⟩

end Consensus.Goldilocks.Healing

end
