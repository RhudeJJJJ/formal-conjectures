/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0659 : Family 10 := level10.get ⟨241,by decide⟩
def sourceMap0659 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0659 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0659_checked : acceptsGraphIso
    (source (graph core0659) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1666.graph sourceMap0659=true := by decide +kernel
theorem fusedMap0659_checked : acceptsGraphIso
    (fused (graph core0659) (root 10) 2 2) DegreeTwoThreeSpectrum5315.graph fusedMap0659=true := by decide +kernel
theorem certified0659 : Certified (graph core0659) (root 10) 2 2 :=
  of_native_maps core0659 DegreeOneMiddleResidualSpectrum1666.graph DegreeTwoThreeSpectrum5315.graph
    sourceMap0659 fusedMap0659 sourceMap0659_checked fusedMap0659_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0659
#print axioms sourceMap0659_checked
#print axioms fusedMap0659_checked
#print axioms certified0659
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
