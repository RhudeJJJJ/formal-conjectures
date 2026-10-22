/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0646 : Family 10 := level10.get ⟨222,by decide⟩
def sourceMap0646 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0646 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0646_checked : acceptsGraphIso
    (source (graph core0646) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1630.graph sourceMap0646=true := by decide +kernel
theorem fusedMap0646_checked : acceptsGraphIso
    (fused (graph core0646) (root 10) 2 2) DegreeTwoThreeSpectrum5254.graph fusedMap0646=true := by decide +kernel
theorem certified0646 : Certified (graph core0646) (root 10) 2 2 :=
  of_native_maps core0646 DegreeOneMiddleResidualSpectrum1630.graph DegreeTwoThreeSpectrum5254.graph
    sourceMap0646 fusedMap0646 sourceMap0646_checked fusedMap0646_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0646
#print axioms sourceMap0646_checked
#print axioms fusedMap0646_checked
#print axioms certified0646
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
