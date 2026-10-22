/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2060 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap2060 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2060 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2060_checked : acceptsGraphIso
    (source (graph core2060) (root 5) 0 4) DegreeOneSmallSpectrum394.graph sourceMap2060=true := by decide +kernel
theorem fusedMap2060_checked : acceptsGraphIso
    (fused (graph core2060) (root 5) 0 4) DegreeOneSmallSpectrum396.graph fusedMap2060=true := by decide +kernel
theorem certified2060 : Certified (graph core2060) (root 5) 0 4 :=
  of_native_maps core2060 DegreeOneSmallSpectrum394.graph DegreeOneSmallSpectrum396.graph
    sourceMap2060 fusedMap2060 sourceMap2060_checked fusedMap2060_checked
    DegreeTwoThreeFiniteComparisons.comparison2060
#print axioms sourceMap2060_checked
#print axioms fusedMap2060_checked
#print axioms certified2060
def sourceMap2060swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,11,6] (sourceLabel 5 4 0 v)
def fusedMap2060swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2060swap_checked : acceptsGraphIso
    (source (graph core2060) (root 5) 4 0) DegreeOneSmallSpectrum394.graph sourceMap2060swap=true := by decide +kernel
theorem fusedMap2060swap_checked : acceptsGraphIso
    (fused (graph core2060) (root 5) 4 0) DegreeOneSmallSpectrum396.graph fusedMap2060swap=true := by decide +kernel
theorem certified2060swap : Certified (graph core2060) (root 5) 4 0 :=
  of_native_maps core2060 DegreeOneSmallSpectrum394.graph DegreeOneSmallSpectrum396.graph
    sourceMap2060swap fusedMap2060swap sourceMap2060swap_checked fusedMap2060swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2060
#print axioms sourceMap2060swap_checked
#print axioms fusedMap2060swap_checked
#print axioms certified2060swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
