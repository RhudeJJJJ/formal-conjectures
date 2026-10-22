/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0802 : Family 10 := level10.get ⟨498,by decide⟩
def sourceMap0802 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0802 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0802_checked : acceptsGraphIso
    (source (graph core0802) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1964.graph sourceMap0802=true := by decide +kernel
theorem fusedMap0802_checked : acceptsGraphIso
    (fused (graph core0802) (root 10) 2 2) DegreeTwoThreeSpectrum5135.graph fusedMap0802=true := by decide +kernel
theorem certified0802 : Certified (graph core0802) (root 10) 2 2 :=
  of_native_maps core0802 DegreeOneMiddleResidualSpectrum1964.graph DegreeTwoThreeSpectrum5135.graph
    sourceMap0802 fusedMap0802 sourceMap0802_checked fusedMap0802_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0802
#print axioms sourceMap0802_checked
#print axioms fusedMap0802_checked
#print axioms certified0802
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
