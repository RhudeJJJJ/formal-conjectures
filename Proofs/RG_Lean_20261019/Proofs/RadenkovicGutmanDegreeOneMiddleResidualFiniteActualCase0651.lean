/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0651 : Family 10 := level10.get ⟨228,by decide⟩
def sourceMap0651 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0651 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0651_checked : acceptsGraphIso
    (source (graph core0651) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1644.graph sourceMap0651=true := by decide +kernel
theorem fusedMap0651_checked : acceptsGraphIso
    (fused (graph core0651) (root 10) 2 2) DegreeTwoThreeSpectrum5276.graph fusedMap0651=true := by decide +kernel
theorem certified0651 : Certified (graph core0651) (root 10) 2 2 :=
  of_native_maps core0651 DegreeOneMiddleResidualSpectrum1644.graph DegreeTwoThreeSpectrum5276.graph
    sourceMap0651 fusedMap0651 sourceMap0651_checked fusedMap0651_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0651
#print axioms sourceMap0651_checked
#print axioms fusedMap0651_checked
#print axioms certified0651
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
