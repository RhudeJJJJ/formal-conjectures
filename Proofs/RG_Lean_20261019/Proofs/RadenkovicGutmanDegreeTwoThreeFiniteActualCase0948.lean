/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0948 : Family 10 := level10.get ⟨1576,by decide⟩
def sourceMap0948 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0948 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0948_checked : acceptsGraphIso
    (source (graph core0948) (root 10) 0 0) DegreeTwoThreeSpectrum1698.graph sourceMap0948=true := by decide +kernel
theorem fusedMap0948_checked : acceptsGraphIso
    (fused (graph core0948) (root 10) 0 0) DegreeOneSmallSpectrum1623.graph fusedMap0948=true := by decide +kernel
theorem certified0948 : Certified (graph core0948) (root 10) 0 0 :=
  of_native_maps core0948 DegreeTwoThreeSpectrum1698.graph DegreeOneSmallSpectrum1623.graph
    sourceMap0948 fusedMap0948 sourceMap0948_checked fusedMap0948_checked
    DegreeTwoThreeFiniteComparisons.comparison0948
#print axioms sourceMap0948_checked
#print axioms fusedMap0948_checked
#print axioms certified0948
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
