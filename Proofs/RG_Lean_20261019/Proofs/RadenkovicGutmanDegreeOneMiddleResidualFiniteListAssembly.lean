/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData

namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteListAssembly
open SmallGeFourKeys DegreeOneMiddleResidualFiniteKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem of_batches (Q : SmallGeFourKeys.Key → Prop)
    (h000 : ∀ k ∈ keys000, Q k)
    (h001 : ∀ k ∈ keys001, Q k)
    (h002 : ∀ k ∈ keys002, Q k)
    (h003 : ∀ k ∈ keys003, Q k)
    (h004 : ∀ k ∈ keys004, Q k)
    (h005 : ∀ k ∈ keys005, Q k)
    (h006 : ∀ k ∈ keys006, Q k)
    (h007 : ∀ k ∈ keys007, Q k)
    (h008 : ∀ k ∈ keys008, Q k)
    (h009 : ∀ k ∈ keys009, Q k)
    (h010 : ∀ k ∈ keys010, Q k)
    (h011 : ∀ k ∈ keys011, Q k)
    (h012 : ∀ k ∈ keys012, Q k)
    (h013 : ∀ k ∈ keys013, Q k)
    (h014 : ∀ k ∈ keys014, Q k)
    (h015 : ∀ k ∈ keys015, Q k)
    (h016 : ∀ k ∈ keys016, Q k)
    (h017 : ∀ k ∈ keys017, Q k)
    (h018 : ∀ k ∈ keys018, Q k)
    (h019 : ∀ k ∈ keys019, Q k)
    (h020 : ∀ k ∈ keys020, Q k)
    (h021 : ∀ k ∈ keys021, Q k)
    (h022 : ∀ k ∈ keys022, Q k)
    (h023 : ∀ k ∈ keys023, Q k)
    (h024 : ∀ k ∈ keys024, Q k)
    : ∀ k ∈ DegreeOneMiddleResidualFiniteKeys.keys, Q k := by
  intro k hk
  rcases List.mem_append.mp hk with h | hk
  · exact h000 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h001 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h002 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h003 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h004 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h005 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h006 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h007 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h008 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h009 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h010 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h011 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h012 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h013 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h014 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h015 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h016 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h017 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h018 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h019 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h020 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h021 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h022 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h023 k h
  rcases List.mem_append.mp hk with h | hk
  · exact h024 k h
  exact False.elim (List.not_mem_nil k hk)

#print axioms of_batches
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteListAssembly
