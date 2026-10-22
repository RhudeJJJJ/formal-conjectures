/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0654 : Family 10 := level10.get ⟨232,by decide⟩
def sourceMap0654 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0654 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0654_checked : acceptsGraphIso
    (source (graph core0654) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1648.graph sourceMap0654=true := by decide +kernel
theorem fusedMap0654_checked : acceptsGraphIso
    (fused (graph core0654) (root 10) 2 2) DegreeTwoThreeSpectrum5288.graph fusedMap0654=true := by decide +kernel
theorem certified0654 : Certified (graph core0654) (root 10) 2 2 :=
  of_native_maps core0654 DegreeOneMiddleResidualSpectrum1648.graph DegreeTwoThreeSpectrum5288.graph
    sourceMap0654 fusedMap0654 sourceMap0654_checked fusedMap0654_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0654
#print axioms sourceMap0654_checked
#print axioms fusedMap0654_checked
#print axioms certified0654
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
