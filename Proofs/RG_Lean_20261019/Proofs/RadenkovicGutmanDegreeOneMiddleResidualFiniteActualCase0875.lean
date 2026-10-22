/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0875 : Family 10 := level10.get ⟨621,by decide⟩
def sourceMap0875 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0875 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0875_checked : acceptsGraphIso
    (source (graph core0875) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2115.graph sourceMap0875=true := by decide +kernel
theorem fusedMap0875_checked : acceptsGraphIso
    (fused (graph core0875) (root 10) 2 2) DegreeTwoThreeSpectrum5312.graph fusedMap0875=true := by decide +kernel
theorem certified0875 : Certified (graph core0875) (root 10) 2 2 :=
  of_native_maps core0875 DegreeOneMiddleResidualSpectrum2115.graph DegreeTwoThreeSpectrum5312.graph
    sourceMap0875 fusedMap0875 sourceMap0875_checked fusedMap0875_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0875
#print axioms sourceMap0875_checked
#print axioms fusedMap0875_checked
#print axioms certified0875
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
