/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0040 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap0040 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0040 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap0040_checked : acceptsGraphIso
    (source (graph core0040) (root 7) 0 0) DegreeOneSmallSpectrum141.graph sourceMap0040=true := by decide +kernel
theorem fusedMap0040_checked : acceptsGraphIso
    (fused (graph core0040) (root 7) 0 0) DegreeOneSmallSpectrum136.graph fusedMap0040=true := by decide +kernel
theorem certified0040 : Certified (graph core0040) (root 7) 0 0 :=
  of_native_maps core0040 DegreeOneSmallSpectrum141.graph DegreeOneSmallSpectrum136.graph
    sourceMap0040 fusedMap0040 sourceMap0040_checked fusedMap0040_checked
    DegreeTwoThreeFiniteComparisons.comparison0040
#print axioms sourceMap0040_checked
#print axioms fusedMap0040_checked
#print axioms certified0040
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
