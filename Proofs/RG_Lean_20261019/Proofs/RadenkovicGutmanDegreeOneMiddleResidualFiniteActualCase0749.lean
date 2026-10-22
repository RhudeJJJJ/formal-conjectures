/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0749 : Family 10 := level10.get ⟨385,by decide⟩
def sourceMap0749 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0749 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0749_checked : acceptsGraphIso
    (source (graph core0749) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1854.graph sourceMap0749=true := by decide +kernel
theorem fusedMap0749_checked : acceptsGraphIso
    (fused (graph core0749) (root 10) 2 2) DegreeTwoThreeSpectrum5718.graph fusedMap0749=true := by decide +kernel
theorem certified0749 : Certified (graph core0749) (root 10) 2 2 :=
  of_native_maps core0749 DegreeOneMiddleResidualSpectrum1854.graph DegreeTwoThreeSpectrum5718.graph
    sourceMap0749 fusedMap0749 sourceMap0749_checked fusedMap0749_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0749
#print axioms sourceMap0749_checked
#print axioms fusedMap0749_checked
#print axioms certified0749
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
