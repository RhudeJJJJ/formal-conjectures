/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0155 : Family 8 := level8.get ⟨164,by decide⟩
def sourceMap0155 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap0155 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0155_checked : acceptsGraphIso
    (source (graph core0155) (root 8) 2 2) DegreeTwoThreeSpectrum3630.graph sourceMap0155=true := by decide +kernel
theorem fusedMap0155_checked : acceptsGraphIso
    (fused (graph core0155) (root 8) 2 2) DegreeTwoThreeSpectrum2834.graph fusedMap0155=true := by decide +kernel
theorem certified0155 : Certified (graph core0155) (root 8) 2 2 :=
  of_native_maps core0155 DegreeTwoThreeSpectrum3630.graph DegreeTwoThreeSpectrum2834.graph
    sourceMap0155 fusedMap0155 sourceMap0155_checked fusedMap0155_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0155
#print axioms sourceMap0155_checked
#print axioms fusedMap0155_checked
#print axioms certified0155
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
