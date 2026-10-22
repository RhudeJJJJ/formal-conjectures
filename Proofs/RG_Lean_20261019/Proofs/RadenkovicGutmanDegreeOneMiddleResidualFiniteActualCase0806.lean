/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0806 : Family 10 := level10.get ⟨503,by decide⟩
def sourceMap0806 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0806 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0806_checked : acceptsGraphIso
    (source (graph core0806) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1975.graph sourceMap0806=true := by decide +kernel
theorem fusedMap0806_checked : acceptsGraphIso
    (fused (graph core0806) (root 10) 2 2) DegreeTwoThreeSpectrum5140.graph fusedMap0806=true := by decide +kernel
theorem certified0806 : Certified (graph core0806) (root 10) 2 2 :=
  of_native_maps core0806 DegreeOneMiddleResidualSpectrum1975.graph DegreeTwoThreeSpectrum5140.graph
    sourceMap0806 fusedMap0806 sourceMap0806_checked fusedMap0806_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0806
#print axioms sourceMap0806_checked
#print axioms fusedMap0806_checked
#print axioms certified0806
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
