/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0567 : Family 10 := level10.get ⟨103,by decide⟩
def sourceMap0567 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0567 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0567_checked : acceptsGraphIso
    (source (graph core0567) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1809.graph sourceMap0567=true := by decide +kernel
theorem fusedMap0567_checked : acceptsGraphIso
    (fused (graph core0567) (root 10) 2 2) DegreeTwoThreeSpectrum5025.graph fusedMap0567=true := by decide +kernel
theorem certified0567 : Certified (graph core0567) (root 10) 2 2 :=
  of_native_maps core0567 DegreeOneMiddleResidualSpectrum1809.graph DegreeTwoThreeSpectrum5025.graph
    sourceMap0567 fusedMap0567 sourceMap0567_checked fusedMap0567_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0567
#print axioms sourceMap0567_checked
#print axioms fusedMap0567_checked
#print axioms certified0567
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
