/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0709 : Family 10 := level10.get ⟨319,by decide⟩
def sourceMap0709 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0709 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0709_checked : acceptsGraphIso
    (source (graph core0709) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1780.graph sourceMap0709=true := by decide +kernel
theorem fusedMap0709_checked : acceptsGraphIso
    (fused (graph core0709) (root 10) 2 2) DegreeTwoThreeSpectrum5533.graph fusedMap0709=true := by decide +kernel
theorem certified0709 : Certified (graph core0709) (root 10) 2 2 :=
  of_native_maps core0709 DegreeOneMiddleResidualSpectrum1780.graph DegreeTwoThreeSpectrum5533.graph
    sourceMap0709 fusedMap0709 sourceMap0709_checked fusedMap0709_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0709
#print axioms sourceMap0709_checked
#print axioms fusedMap0709_checked
#print axioms certified0709
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
