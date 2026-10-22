/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0495 : Family 10 := level10.get ⟨12,by decide⟩
def sourceMap0495 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0495 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0495_checked : acceptsGraphIso
    (source (graph core0495) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1205.graph sourceMap0495=true := by decide +kernel
theorem fusedMap0495_checked : acceptsGraphIso
    (fused (graph core0495) (root 10) 2 2) DegreeTwoThreeSpectrum4987.graph fusedMap0495=true := by decide +kernel
theorem certified0495 : Certified (graph core0495) (root 10) 2 2 :=
  of_native_maps core0495 DegreeOneMiddleResidualSpectrum1205.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap0495 fusedMap0495 sourceMap0495_checked fusedMap0495_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0495
#print axioms sourceMap0495_checked
#print axioms fusedMap0495_checked
#print axioms certified0495
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
