/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0742 : Family 10 := level10.get ⟨376,by decide⟩
def sourceMap0742 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0742 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0742_checked : acceptsGraphIso
    (source (graph core0742) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1900.graph sourceMap0742=true := by decide +kernel
theorem fusedMap0742_checked : acceptsGraphIso
    (fused (graph core0742) (root 10) 2 2) DegreeTwoThreeSpectrum5691.graph fusedMap0742=true := by decide +kernel
theorem certified0742 : Certified (graph core0742) (root 10) 2 2 :=
  of_native_maps core0742 DegreeOneMiddleResidualSpectrum1900.graph DegreeTwoThreeSpectrum5691.graph
    sourceMap0742 fusedMap0742 sourceMap0742_checked fusedMap0742_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0742
#print axioms sourceMap0742_checked
#print axioms fusedMap0742_checked
#print axioms certified0742
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
