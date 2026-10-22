/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0660 : Family 10 := level10.get ⟨242,by decide⟩
def sourceMap0660 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0660 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0660_checked : acceptsGraphIso
    (source (graph core0660) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1669.graph sourceMap0660=true := by decide +kernel
theorem fusedMap0660_checked : acceptsGraphIso
    (fused (graph core0660) (root 10) 2 2) DegreeTwoThreeSpectrum5318.graph fusedMap0660=true := by decide +kernel
theorem certified0660 : Certified (graph core0660) (root 10) 2 2 :=
  of_native_maps core0660 DegreeOneMiddleResidualSpectrum1669.graph DegreeTwoThreeSpectrum5318.graph
    sourceMap0660 fusedMap0660 sourceMap0660_checked fusedMap0660_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0660
#print axioms sourceMap0660_checked
#print axioms fusedMap0660_checked
#print axioms certified0660
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
