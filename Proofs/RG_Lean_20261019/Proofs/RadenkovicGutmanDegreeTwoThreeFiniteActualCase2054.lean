/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2054 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap2054 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (sourceLabel 3 0 3 v)
def fusedMap2054 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 0 3 v)
theorem sourceMap2054_checked : acceptsGraphIso
    (source (graph core2054) (root 3) 0 3) DegreeOneSmallSpectrum058.graph sourceMap2054=true := by decide +kernel
theorem fusedMap2054_checked : acceptsGraphIso
    (fused (graph core2054) (root 3) 0 3) DegreeOneSmallSpectrum035.graph fusedMap2054=true := by decide +kernel
theorem certified2054 : Certified (graph core2054) (root 3) 0 3 :=
  of_native_maps core2054 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum035.graph
    sourceMap2054 fusedMap2054 sourceMap2054_checked fusedMap2054_checked
    DegreeTwoThreeFiniteComparisons.comparison2054
#print axioms sourceMap2054_checked
#print axioms fusedMap2054_checked
#print axioms certified2054
def sourceMap2054swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,2,3,4,0,6,7,8,5] (sourceLabel 3 3 0 v)
def fusedMap2054swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 3 0 v)
theorem sourceMap2054swap_checked : acceptsGraphIso
    (source (graph core2054) (root 3) 3 0) DegreeOneSmallSpectrum058.graph sourceMap2054swap=true := by decide +kernel
theorem fusedMap2054swap_checked : acceptsGraphIso
    (fused (graph core2054) (root 3) 3 0) DegreeOneSmallSpectrum035.graph fusedMap2054swap=true := by decide +kernel
theorem certified2054swap : Certified (graph core2054) (root 3) 3 0 :=
  of_native_maps core2054 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum035.graph
    sourceMap2054swap fusedMap2054swap sourceMap2054swap_checked fusedMap2054swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2054
#print axioms sourceMap2054swap_checked
#print axioms fusedMap2054swap_checked
#print axioms certified2054swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
