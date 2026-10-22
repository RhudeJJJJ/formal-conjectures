/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0614 : Family 10 := level10.get ⟨735,by decide⟩
def sourceMap0614 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0614 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0614_checked : acceptsGraphIso
    (source (graph core0614) (root 10) 0 0) DegreeTwoThreeSpectrum1433.graph sourceMap0614=true := by decide +kernel
theorem fusedMap0614_checked : acceptsGraphIso
    (fused (graph core0614) (root 10) 0 0) DegreeOneSmallSpectrum1359.graph fusedMap0614=true := by decide +kernel
theorem certified0614 : Certified (graph core0614) (root 10) 0 0 :=
  of_native_maps core0614 DegreeTwoThreeSpectrum1433.graph DegreeOneSmallSpectrum1359.graph
    sourceMap0614 fusedMap0614 sourceMap0614_checked fusedMap0614_checked
    DegreeTwoThreeFiniteComparisons.comparison0614
#print axioms sourceMap0614_checked
#print axioms fusedMap0614_checked
#print axioms certified0614
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
