/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0947 : Family 10 := level10.get ⟨769,by decide⟩
def sourceMap0947 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0947 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0947_checked : acceptsGraphIso
    (source (graph core0947) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2232.graph sourceMap0947=true := by decide +kernel
theorem fusedMap0947_checked : acceptsGraphIso
    (fused (graph core0947) (root 10) 2 2) DegreeTwoThreeSpectrum5547.graph fusedMap0947=true := by decide +kernel
theorem certified0947 : Certified (graph core0947) (root 10) 2 2 :=
  of_native_maps core0947 DegreeOneMiddleResidualSpectrum2232.graph DegreeTwoThreeSpectrum5547.graph
    sourceMap0947 fusedMap0947 sourceMap0947_checked fusedMap0947_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0947
#print axioms sourceMap0947_checked
#print axioms fusedMap0947_checked
#print axioms certified0947
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
