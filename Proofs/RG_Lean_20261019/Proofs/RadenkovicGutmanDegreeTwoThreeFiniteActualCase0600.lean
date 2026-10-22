/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0600 : Family 10 := level10.get ⟨694,by decide⟩
def sourceMap0600 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0600 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0600_checked : acceptsGraphIso
    (source (graph core0600) (root 10) 0 0) DegreeTwoThreeSpectrum1462.graph sourceMap0600=true := by decide +kernel
theorem fusedMap0600_checked : acceptsGraphIso
    (fused (graph core0600) (root 10) 0 0) DegreeOneSmallSpectrum1304.graph fusedMap0600=true := by decide +kernel
theorem certified0600 : Certified (graph core0600) (root 10) 0 0 :=
  of_native_maps core0600 DegreeTwoThreeSpectrum1462.graph DegreeOneSmallSpectrum1304.graph
    sourceMap0600 fusedMap0600 sourceMap0600_checked fusedMap0600_checked
    DegreeTwoThreeFiniteComparisons.comparison0600
#print axioms sourceMap0600_checked
#print axioms fusedMap0600_checked
#print axioms certified0600
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
