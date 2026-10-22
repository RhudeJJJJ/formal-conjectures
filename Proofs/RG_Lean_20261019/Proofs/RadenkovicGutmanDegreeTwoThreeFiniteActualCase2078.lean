/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2078 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap2078 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2078 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2078_checked : acceptsGraphIso
    (source (graph core2078) (root 6) 0 4) DegreeOneSmallSpectrum1471.graph sourceMap2078=true := by decide +kernel
theorem fusedMap2078_checked : acceptsGraphIso
    (fused (graph core2078) (root 6) 0 4) DegreeOneSmallSpectrum946.graph fusedMap2078=true := by decide +kernel
theorem certified2078 : Certified (graph core2078) (root 6) 0 4 :=
  of_native_maps core2078 DegreeOneSmallSpectrum1471.graph DegreeOneSmallSpectrum946.graph
    sourceMap2078 fusedMap2078 sourceMap2078_checked fusedMap2078_checked
    DegreeTwoThreeFiniteComparisons.comparison2078
#print axioms sourceMap2078_checked
#print axioms fusedMap2078_checked
#print axioms certified2078
def sourceMap2078swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2078swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2078swap_checked : acceptsGraphIso
    (source (graph core2078) (root 6) 4 0) DegreeOneSmallSpectrum1471.graph sourceMap2078swap=true := by decide +kernel
theorem fusedMap2078swap_checked : acceptsGraphIso
    (fused (graph core2078) (root 6) 4 0) DegreeOneSmallSpectrum946.graph fusedMap2078swap=true := by decide +kernel
theorem certified2078swap : Certified (graph core2078) (root 6) 4 0 :=
  of_native_maps core2078 DegreeOneSmallSpectrum1471.graph DegreeOneSmallSpectrum946.graph
    sourceMap2078swap fusedMap2078swap sourceMap2078swap_checked fusedMap2078swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2078
#print axioms sourceMap2078swap_checked
#print axioms fusedMap2078swap_checked
#print axioms certified2078swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
