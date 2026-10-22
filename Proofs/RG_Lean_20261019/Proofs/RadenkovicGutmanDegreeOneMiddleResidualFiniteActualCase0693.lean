/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0693 : Family 10 := level10.get ⟨296,by decide⟩
def sourceMap0693 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0693 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0693_checked : acceptsGraphIso
    (source (graph core0693) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1742.graph sourceMap0693=true := by decide +kernel
theorem fusedMap0693_checked : acceptsGraphIso
    (fused (graph core0693) (root 10) 2 2) DegreeTwoThreeSpectrum5465.graph fusedMap0693=true := by decide +kernel
theorem certified0693 : Certified (graph core0693) (root 10) 2 2 :=
  of_native_maps core0693 DegreeOneMiddleResidualSpectrum1742.graph DegreeTwoThreeSpectrum5465.graph
    sourceMap0693 fusedMap0693 sourceMap0693_checked fusedMap0693_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0693
#print axioms sourceMap0693_checked
#print axioms fusedMap0693_checked
#print axioms certified0693
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
