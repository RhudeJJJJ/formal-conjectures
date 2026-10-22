/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0566 : Family 10 := level10.get ⟨102,by decide⟩
def sourceMap0566 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0566 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0566_checked : acceptsGraphIso
    (source (graph core0566) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1810.graph sourceMap0566=true := by decide +kernel
theorem fusedMap0566_checked : acceptsGraphIso
    (fused (graph core0566) (root 10) 2 2) DegreeTwoThreeSpectrum5024.graph fusedMap0566=true := by decide +kernel
theorem certified0566 : Certified (graph core0566) (root 10) 2 2 :=
  of_native_maps core0566 DegreeOneMiddleResidualSpectrum1810.graph DegreeTwoThreeSpectrum5024.graph
    sourceMap0566 fusedMap0566 sourceMap0566_checked fusedMap0566_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0566
#print axioms sourceMap0566_checked
#print axioms fusedMap0566_checked
#print axioms certified0566
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
