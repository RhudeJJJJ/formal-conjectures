/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2064 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap2064 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2064 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2064_checked : acceptsGraphIso
    (source (graph core2064) (root 5) 0 4) DegreeOneSmallSpectrum406.graph sourceMap2064=true := by decide +kernel
theorem fusedMap2064_checked : acceptsGraphIso
    (fused (graph core2064) (root 5) 0 4) DegreeOneSmallSpectrum411.graph fusedMap2064=true := by decide +kernel
theorem certified2064 : Certified (graph core2064) (root 5) 0 4 :=
  of_native_maps core2064 DegreeOneSmallSpectrum406.graph DegreeOneSmallSpectrum411.graph
    sourceMap2064 fusedMap2064 sourceMap2064_checked fusedMap2064_checked
    DegreeTwoThreeFiniteComparisons.comparison2064
#print axioms sourceMap2064_checked
#print axioms fusedMap2064_checked
#print axioms certified2064
def sourceMap2064swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap2064swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2064swap_checked : acceptsGraphIso
    (source (graph core2064) (root 5) 4 0) DegreeOneSmallSpectrum406.graph sourceMap2064swap=true := by decide +kernel
theorem fusedMap2064swap_checked : acceptsGraphIso
    (fused (graph core2064) (root 5) 4 0) DegreeOneSmallSpectrum411.graph fusedMap2064swap=true := by decide +kernel
theorem certified2064swap : Certified (graph core2064) (root 5) 4 0 :=
  of_native_maps core2064 DegreeOneSmallSpectrum406.graph DegreeOneSmallSpectrum411.graph
    sourceMap2064swap fusedMap2064swap sourceMap2064swap_checked fusedMap2064swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2064
#print axioms sourceMap2064swap_checked
#print axioms fusedMap2064swap_checked
#print axioms certified2064swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
