import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF,
    ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  let y := PEqualNP.MetaComplexity.CoverPromise.fresh φ
  have hy : y ∈ PEqualNP.MetaComplexity.CoverPromise.vars
      (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) := by
    unfold PEqualNP.MetaComplexity.CoverPromise.vars
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨[(y, false)], ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.CoverPromise.cvcFormula, y]
    · simp
  refine ⟨Sum.inl (y, true), Sum.inl (y, false), ?_⟩
  change y = y ∧ true ≠ false ∧ y ∈ PEqualNP.MetaComplexity.CoverPromise.vars
    (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)
  exact ⟨rfl, by decide, hy⟩
