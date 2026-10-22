/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0717 : Family 10 := level10.get ⟨1002,by decide⟩
def sourceMap0717 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0717 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0717_checked : acceptsGraphIso
    (source (graph core0717) (root 10) 0 0) DegreeTwoThreeSpectrum1295.graph sourceMap0717=true := by decide +kernel
theorem fusedMap0717_checked : acceptsGraphIso
    (fused (graph core0717) (root 10) 0 0) DegreeOneSmallSpectrum1544.graph fusedMap0717=true := by decide +kernel
theorem certified0717 : Certified (graph core0717) (root 10) 0 0 :=
  of_native_maps core0717 DegreeTwoThreeSpectrum1295.graph DegreeOneSmallSpectrum1544.graph
    sourceMap0717 fusedMap0717 sourceMap0717_checked fusedMap0717_checked
    DegreeTwoThreeFiniteComparisons.comparison0717
#print axioms sourceMap0717_checked
#print axioms fusedMap0717_checked
#print axioms certified0717
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
