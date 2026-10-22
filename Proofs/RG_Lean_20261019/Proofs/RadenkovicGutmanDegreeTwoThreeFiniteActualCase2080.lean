/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2080 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap2080 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2080 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2080_checked : acceptsGraphIso
    (source (graph core2080) (root 6) 0 4) DegreeOneSmallSpectrum1010.graph sourceMap2080=true := by decide +kernel
theorem fusedMap2080_checked : acceptsGraphIso
    (fused (graph core2080) (root 6) 0 4) DegreeOneSmallSpectrum1015.graph fusedMap2080=true := by decide +kernel
theorem certified2080 : Certified (graph core2080) (root 6) 0 4 :=
  of_native_maps core2080 DegreeOneSmallSpectrum1010.graph DegreeOneSmallSpectrum1015.graph
    sourceMap2080 fusedMap2080 sourceMap2080_checked fusedMap2080_checked
    DegreeTwoThreeFiniteComparisons.comparison2080
#print axioms sourceMap2080_checked
#print axioms fusedMap2080_checked
#print axioms certified2080
def sourceMap2080swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2080swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2080swap_checked : acceptsGraphIso
    (source (graph core2080) (root 6) 4 0) DegreeOneSmallSpectrum1010.graph sourceMap2080swap=true := by decide +kernel
theorem fusedMap2080swap_checked : acceptsGraphIso
    (fused (graph core2080) (root 6) 4 0) DegreeOneSmallSpectrum1015.graph fusedMap2080swap=true := by decide +kernel
theorem certified2080swap : Certified (graph core2080) (root 6) 4 0 :=
  of_native_maps core2080 DegreeOneSmallSpectrum1010.graph DegreeOneSmallSpectrum1015.graph
    sourceMap2080swap fusedMap2080swap sourceMap2080swap_checked fusedMap2080swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2080
#print axioms sourceMap2080swap_checked
#print axioms fusedMap2080swap_checked
#print axioms certified2080swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
