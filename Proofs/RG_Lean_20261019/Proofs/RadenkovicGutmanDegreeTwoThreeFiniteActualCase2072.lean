/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2072 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap2072 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2072 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2072_checked : acceptsGraphIso
    (source (graph core2072) (root 6) 0 4) DegreeOneSmallSpectrum1147.graph sourceMap2072=true := by decide +kernel
theorem fusedMap2072_checked : acceptsGraphIso
    (fused (graph core2072) (root 6) 0 4) DegreeOneSmallSpectrum873.graph fusedMap2072=true := by decide +kernel
theorem certified2072 : Certified (graph core2072) (root 6) 0 4 :=
  of_native_maps core2072 DegreeOneSmallSpectrum1147.graph DegreeOneSmallSpectrum873.graph
    sourceMap2072 fusedMap2072 sourceMap2072_checked fusedMap2072_checked
    DegreeTwoThreeFiniteComparisons.comparison2072
#print axioms sourceMap2072_checked
#print axioms fusedMap2072_checked
#print axioms certified2072
def sourceMap2072swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2072swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2072swap_checked : acceptsGraphIso
    (source (graph core2072) (root 6) 4 0) DegreeOneSmallSpectrum1147.graph sourceMap2072swap=true := by decide +kernel
theorem fusedMap2072swap_checked : acceptsGraphIso
    (fused (graph core2072) (root 6) 4 0) DegreeOneSmallSpectrum873.graph fusedMap2072swap=true := by decide +kernel
theorem certified2072swap : Certified (graph core2072) (root 6) 4 0 :=
  of_native_maps core2072 DegreeOneSmallSpectrum1147.graph DegreeOneSmallSpectrum873.graph
    sourceMap2072swap fusedMap2072swap sourceMap2072swap_checked fusedMap2072swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2072
#print axioms sourceMap2072swap_checked
#print axioms fusedMap2072swap_checked
#print axioms certified2072swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
