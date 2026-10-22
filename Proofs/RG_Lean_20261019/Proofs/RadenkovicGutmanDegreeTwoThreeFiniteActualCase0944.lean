/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0944 : Family 10 := level10.get ⟨1567,by decide⟩
def sourceMap0944 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0944 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0944_checked : acceptsGraphIso
    (source (graph core0944) (root 10) 0 0) DegreeTwoThreeSpectrum1695.graph sourceMap0944=true := by decide +kernel
theorem fusedMap0944_checked : acceptsGraphIso
    (fused (graph core0944) (root 10) 0 0) DegreeOneSmallSpectrum1603.graph fusedMap0944=true := by decide +kernel
theorem certified0944 : Certified (graph core0944) (root 10) 0 0 :=
  of_native_maps core0944 DegreeTwoThreeSpectrum1695.graph DegreeOneSmallSpectrum1603.graph
    sourceMap0944 fusedMap0944 sourceMap0944_checked fusedMap0944_checked
    DegreeTwoThreeFiniteComparisons.comparison0944
#print axioms sourceMap0944_checked
#print axioms fusedMap0944_checked
#print axioms certified0944
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
