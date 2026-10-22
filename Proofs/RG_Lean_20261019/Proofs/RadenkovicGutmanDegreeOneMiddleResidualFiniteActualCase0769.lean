/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0769 : Family 10 := level10.get ⟨418,by decide⟩
def sourceMap0769 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0769 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0769_checked : acceptsGraphIso
    (source (graph core0769) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1851.graph sourceMap0769=true := by decide +kernel
theorem fusedMap0769_checked : acceptsGraphIso
    (fused (graph core0769) (root 10) 2 2) DegreeTwoThreeSpectrum5802.graph fusedMap0769=true := by decide +kernel
theorem certified0769 : Certified (graph core0769) (root 10) 2 2 :=
  of_native_maps core0769 DegreeOneMiddleResidualSpectrum1851.graph DegreeTwoThreeSpectrum5802.graph
    sourceMap0769 fusedMap0769 sourceMap0769_checked fusedMap0769_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0769
#print axioms sourceMap0769_checked
#print axioms fusedMap0769_checked
#print axioms certified0769
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
