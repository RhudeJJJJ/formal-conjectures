/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0616 : Family 10 := level10.get ⟨742,by decide⟩
def sourceMap0616 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0616 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0616_checked : acceptsGraphIso
    (source (graph core0616) (root 10) 0 0) DegreeTwoThreeSpectrum1468.graph sourceMap0616=true := by decide +kernel
theorem fusedMap0616_checked : acceptsGraphIso
    (fused (graph core0616) (root 10) 0 0) DegreeOneSmallSpectrum1368.graph fusedMap0616=true := by decide +kernel
theorem certified0616 : Certified (graph core0616) (root 10) 0 0 :=
  of_native_maps core0616 DegreeTwoThreeSpectrum1468.graph DegreeOneSmallSpectrum1368.graph
    sourceMap0616 fusedMap0616 sourceMap0616_checked fusedMap0616_checked
    DegreeTwoThreeFiniteComparisons.comparison0616
#print axioms sourceMap0616_checked
#print axioms fusedMap0616_checked
#print axioms certified0616
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
