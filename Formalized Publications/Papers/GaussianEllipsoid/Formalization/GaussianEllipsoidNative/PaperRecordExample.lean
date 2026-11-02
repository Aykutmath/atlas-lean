import GreedyRecords

namespace GaussianEllipsoidCandidate

/-- Paper's worked example (lines 1867–1879): the genuine greedy grouping
certificate, using precisely the successive support cardinalities 1,1,3,2,10. -/
theorem paper_record_grouping_example :
    RecordGrouping (fun k : ℕ => k) [1,1,3,2,10] [[1,1],[3,2],[10]] := by
  refine RecordGrouping.cons 1 [1] [3,2,10] [[3,2],[10]] ?_ ?_ ?_
  · simp
  · intro b tail h
    simp_all <;> omega
  · refine RecordGrouping.cons 3 [2] [10] [[10]] ?_ ?_ ?_
    · simp
    · intro b tail h
      simp_all <;> omega
    · refine RecordGrouping.cons 10 [] [] [] ?_ ?_ RecordGrouping.nil
      · simp
      · simp

/-- The three selected record sizes, without guessing from the theorem name. -/
theorem paper_record_heads_example :
    ([[1,1],[3,2],[10]] : List (List ℕ)).filterMap List.head? = [1,3,10] := by
  rfl

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_record_grouping_example
#print axioms GaussianEllipsoidCandidate.paper_record_heads_example
