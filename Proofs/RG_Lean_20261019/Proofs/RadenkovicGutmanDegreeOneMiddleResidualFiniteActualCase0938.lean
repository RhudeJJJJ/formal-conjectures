/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0938 : Family 10 := level10.get ⟨751,by decide⟩
def sourceMap0938 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0938 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0938_checked : acceptsGraphIso
    (source (graph core0938) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2216.graph sourceMap0938=true := by decide +kernel
theorem fusedMap0938_checked : acceptsGraphIso
    (fused (graph core0938) (root 10) 2 2) DegreeTwoThreeSpectrum5517.graph fusedMap0938=true := by decide +kernel
theorem certified0938 : Certified (graph core0938) (root 10) 2 2 :=
  of_native_maps core0938 DegreeOneMiddleResidualSpectrum2216.graph DegreeTwoThreeSpectrum5517.graph
    sourceMap0938 fusedMap0938 sourceMap0938_checked fusedMap0938_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0938
#print axioms sourceMap0938_checked
#print axioms fusedMap0938_checked
#print axioms certified0938
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
