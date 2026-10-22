/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0595 : Family 10 := level10.get ⟨141,by decide⟩
def sourceMap0595 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0595 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0595_checked : acceptsGraphIso
    (source (graph core0595) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1869.graph sourceMap0595=true := by decide +kernel
theorem fusedMap0595_checked : acceptsGraphIso
    (fused (graph core0595) (root 10) 2 2) DegreeTwoThreeSpectrum5073.graph fusedMap0595=true := by decide +kernel
theorem certified0595 : Certified (graph core0595) (root 10) 2 2 :=
  of_native_maps core0595 DegreeOneMiddleResidualSpectrum1869.graph DegreeTwoThreeSpectrum5073.graph
    sourceMap0595 fusedMap0595 sourceMap0595_checked fusedMap0595_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0595
#print axioms sourceMap0595_checked
#print axioms fusedMap0595_checked
#print axioms certified0595
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
