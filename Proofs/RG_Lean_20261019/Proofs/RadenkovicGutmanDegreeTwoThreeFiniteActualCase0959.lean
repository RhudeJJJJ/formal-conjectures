/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0959 : Family 10 := level10.get ⟨1599,by decide⟩
def sourceMap0959 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0959 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0959_checked : acceptsGraphIso
    (source (graph core0959) (root 10) 0 0) DegreeTwoThreeSpectrum1442.graph sourceMap0959=true := by decide +kernel
theorem fusedMap0959_checked : acceptsGraphIso
    (fused (graph core0959) (root 10) 0 0) DegreeTwoThreeSpectrum1441.graph fusedMap0959=true := by decide +kernel
theorem certified0959 : Certified (graph core0959) (root 10) 0 0 :=
  of_native_maps core0959 DegreeTwoThreeSpectrum1442.graph DegreeTwoThreeSpectrum1441.graph
    sourceMap0959 fusedMap0959 sourceMap0959_checked fusedMap0959_checked
    DegreeTwoThreeFiniteComparisons.comparison0959
#print axioms sourceMap0959_checked
#print axioms fusedMap0959_checked
#print axioms certified0959
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
