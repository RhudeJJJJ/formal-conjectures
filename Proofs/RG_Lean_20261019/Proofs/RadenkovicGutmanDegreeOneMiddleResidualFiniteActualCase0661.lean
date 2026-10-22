/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0661 : Family 10 := level10.get ⟨243,by decide⟩
def sourceMap0661 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0661 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0661_checked : acceptsGraphIso
    (source (graph core0661) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1670.graph sourceMap0661=true := by decide +kernel
theorem fusedMap0661_checked : acceptsGraphIso
    (fused (graph core0661) (root 10) 2 2) DegreeTwoThreeSpectrum5322.graph fusedMap0661=true := by decide +kernel
theorem certified0661 : Certified (graph core0661) (root 10) 2 2 :=
  of_native_maps core0661 DegreeOneMiddleResidualSpectrum1670.graph DegreeTwoThreeSpectrum5322.graph
    sourceMap0661 fusedMap0661 sourceMap0661_checked fusedMap0661_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0661
#print axioms sourceMap0661_checked
#print axioms fusedMap0661_checked
#print axioms certified0661
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
