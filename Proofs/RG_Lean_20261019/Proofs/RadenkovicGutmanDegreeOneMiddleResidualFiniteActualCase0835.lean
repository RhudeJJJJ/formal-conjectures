/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0835 : Family 10 := level10.get ⟨548,by decide⟩
def sourceMap0835 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0835 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0835_checked : acceptsGraphIso
    (source (graph core0835) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2034.graph sourceMap0835=true := by decide +kernel
theorem fusedMap0835_checked : acceptsGraphIso
    (fused (graph core0835) (root 10) 2 2) DegreeTwoThreeSpectrum5202.graph fusedMap0835=true := by decide +kernel
theorem certified0835 : Certified (graph core0835) (root 10) 2 2 :=
  of_native_maps core0835 DegreeOneMiddleResidualSpectrum2034.graph DegreeTwoThreeSpectrum5202.graph
    sourceMap0835 fusedMap0835 sourceMap0835_checked fusedMap0835_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0835
#print axioms sourceMap0835_checked
#print axioms fusedMap0835_checked
#print axioms certified0835
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
