/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0557 : Family 10 := level10.get ⟨91,by decide⟩
def sourceMap0557 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0557 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0557_checked : acceptsGraphIso
    (source (graph core0557) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1747.graph sourceMap0557=true := by decide +kernel
theorem fusedMap0557_checked : acceptsGraphIso
    (fused (graph core0557) (root 10) 2 2) DegreeTwoThreeSpectrum5012.graph fusedMap0557=true := by decide +kernel
theorem certified0557 : Certified (graph core0557) (root 10) 2 2 :=
  of_native_maps core0557 DegreeOneMiddleResidualSpectrum1747.graph DegreeTwoThreeSpectrum5012.graph
    sourceMap0557 fusedMap0557 sourceMap0557_checked fusedMap0557_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0557
#print axioms sourceMap0557_checked
#print axioms fusedMap0557_checked
#print axioms certified0557
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
