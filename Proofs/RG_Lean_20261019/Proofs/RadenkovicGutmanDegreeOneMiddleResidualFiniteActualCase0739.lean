/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0739 : Family 10 := level10.get ⟨372,by decide⟩
def sourceMap0739 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0739 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0739_checked : acceptsGraphIso
    (source (graph core0739) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1897.graph sourceMap0739=true := by decide +kernel
theorem fusedMap0739_checked : acceptsGraphIso
    (fused (graph core0739) (root 10) 2 2) DegreeTwoThreeSpectrum5679.graph fusedMap0739=true := by decide +kernel
theorem certified0739 : Certified (graph core0739) (root 10) 2 2 :=
  of_native_maps core0739 DegreeOneMiddleResidualSpectrum1897.graph DegreeTwoThreeSpectrum5679.graph
    sourceMap0739 fusedMap0739 sourceMap0739_checked fusedMap0739_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0739
#print axioms sourceMap0739_checked
#print axioms fusedMap0739_checked
#print axioms certified0739
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
