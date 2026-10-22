/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0725 : Family 10 := level10.get ⟨1025,by decide⟩
def sourceMap0725 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0725 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0725_checked : acceptsGraphIso
    (source (graph core0725) (root 10) 0 0) DegreeTwoThreeSpectrum1338.graph sourceMap0725=true := by decide +kernel
theorem fusedMap0725_checked : acceptsGraphIso
    (fused (graph core0725) (root 10) 0 0) DegreeOneSmallSpectrum1596.graph fusedMap0725=true := by decide +kernel
theorem certified0725 : Certified (graph core0725) (root 10) 0 0 :=
  of_native_maps core0725 DegreeTwoThreeSpectrum1338.graph DegreeOneSmallSpectrum1596.graph
    sourceMap0725 fusedMap0725 sourceMap0725_checked fusedMap0725_checked
    DegreeTwoThreeFiniteComparisons.comparison0725
#print axioms sourceMap0725_checked
#print axioms fusedMap0725_checked
#print axioms certified0725
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
