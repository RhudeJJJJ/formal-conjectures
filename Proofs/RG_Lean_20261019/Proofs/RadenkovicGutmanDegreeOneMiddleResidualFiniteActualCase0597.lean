/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0597 : Family 10 := level10.get ⟨146,by decide⟩
def sourceMap0597 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0597 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0597_checked : acceptsGraphIso
    (source (graph core0597) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1931.graph sourceMap0597=true := by decide +kernel
theorem fusedMap0597_checked : acceptsGraphIso
    (fused (graph core0597) (root 10) 2 2) DegreeTwoThreeSpectrum5082.graph fusedMap0597=true := by decide +kernel
theorem certified0597 : Certified (graph core0597) (root 10) 2 2 :=
  of_native_maps core0597 DegreeOneMiddleResidualSpectrum1931.graph DegreeTwoThreeSpectrum5082.graph
    sourceMap0597 fusedMap0597 sourceMap0597_checked fusedMap0597_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0597
#print axioms sourceMap0597_checked
#print axioms fusedMap0597_checked
#print axioms certified0597
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
