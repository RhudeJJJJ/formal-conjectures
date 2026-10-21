/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0023 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap0023 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap0023 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,3,4,5] (fusedLabel 6 0 0 v)
theorem sourceMap0023_checked : acceptsGraphIso
    (source (graph core0023) (root 6) 0 0) DegreeOneSmallSpectrum044.graph sourceMap0023=true := by decide +kernel
theorem fusedMap0023_checked : acceptsGraphIso
    (fused (graph core0023) (root 6) 0 0) DegreeOneSmallSpectrum043.graph fusedMap0023=true := by decide +kernel
theorem certified0023 : Certified (graph core0023) (root 6) 0 0 :=
  of_native_maps core0023 DegreeOneSmallSpectrum044.graph DegreeOneSmallSpectrum043.graph
    sourceMap0023 fusedMap0023 sourceMap0023_checked fusedMap0023_checked
    DegreeTwoThreeFiniteComparisons.comparison0023
#print axioms sourceMap0023_checked
#print axioms fusedMap0023_checked
#print axioms certified0023
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
