/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0833 : Family 10 := level10.get ⟨543,by decide⟩
def sourceMap0833 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0833 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0833_checked : acceptsGraphIso
    (source (graph core0833) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2032.graph sourceMap0833=true := by decide +kernel
theorem fusedMap0833_checked : acceptsGraphIso
    (fused (graph core0833) (root 10) 2 2) DegreeTwoThreeSpectrum5193.graph fusedMap0833=true := by decide +kernel
theorem certified0833 : Certified (graph core0833) (root 10) 2 2 :=
  of_native_maps core0833 DegreeOneMiddleResidualSpectrum2032.graph DegreeTwoThreeSpectrum5193.graph
    sourceMap0833 fusedMap0833 sourceMap0833_checked fusedMap0833_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0833
#print axioms sourceMap0833_checked
#print axioms fusedMap0833_checked
#print axioms certified0833
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
