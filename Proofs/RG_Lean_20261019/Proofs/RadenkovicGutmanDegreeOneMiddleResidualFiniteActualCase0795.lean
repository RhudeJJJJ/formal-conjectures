/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0795 : Family 10 := level10.get ⟨470,by decide⟩
def sourceMap0795 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0795 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0795_checked : acceptsGraphIso
    (source (graph core0795) (root 10) 2 2) DegreeTwoThreeSpectrum6858.graph sourceMap0795=true := by decide +kernel
theorem fusedMap0795_checked : acceptsGraphIso
    (fused (graph core0795) (root 10) 2 2) DegreeTwoThreeSpectrum5925.graph fusedMap0795=true := by decide +kernel
theorem certified0795 : Certified (graph core0795) (root 10) 2 2 :=
  of_native_maps core0795 DegreeTwoThreeSpectrum6858.graph DegreeTwoThreeSpectrum5925.graph
    sourceMap0795 fusedMap0795 sourceMap0795_checked fusedMap0795_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0795
#print axioms sourceMap0795_checked
#print axioms fusedMap0795_checked
#print axioms certified0795
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
