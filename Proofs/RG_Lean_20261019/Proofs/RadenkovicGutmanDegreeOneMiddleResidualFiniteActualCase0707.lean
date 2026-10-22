/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0707 : Family 10 := level10.get ⟨316,by decide⟩
def sourceMap0707 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0707 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0707_checked : acceptsGraphIso
    (source (graph core0707) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1777.graph sourceMap0707=true := by decide +kernel
theorem fusedMap0707_checked : acceptsGraphIso
    (fused (graph core0707) (root 10) 2 2) DegreeTwoThreeSpectrum5526.graph fusedMap0707=true := by decide +kernel
theorem certified0707 : Certified (graph core0707) (root 10) 2 2 :=
  of_native_maps core0707 DegreeOneMiddleResidualSpectrum1777.graph DegreeTwoThreeSpectrum5526.graph
    sourceMap0707 fusedMap0707 sourceMap0707_checked fusedMap0707_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0707
#print axioms sourceMap0707_checked
#print axioms fusedMap0707_checked
#print axioms certified0707
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
