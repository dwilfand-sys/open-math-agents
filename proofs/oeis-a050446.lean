import OMAStatements.S_oeis_a050446

-- Credit: @dwilfand-sys. OEIS A050446, row two, column one.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) := by
  intro h
  have htable : OMA.S_oeis_a050446.tableValue 2 1 = 3 := by decide
  have hword : OMA.S_oeis_a050446.wordCount 2 1 = 1 := by decide
  have heq := h 2 1
  omega
