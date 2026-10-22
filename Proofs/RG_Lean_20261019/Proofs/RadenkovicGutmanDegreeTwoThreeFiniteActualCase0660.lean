/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0660 : Family 10 := level10.get ⟨861,by decide⟩
def sourceMap0660 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0660 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0660_checked : acceptsGraphIso
    (source (graph core0660) (root 10) 0 0) DegreeOneSmallSpectrum1387.graph sourceMap0660=true := by decide +kernel
theorem fusedMap0660_checked : acceptsGraphIso
    (fused (graph core0660) (root 10) 0 0) DegreeOneSmallSpectrum1342.graph fusedMap0660=true := by decide +kernel
theorem certified0660 : Certified (graph core0660) (root 10) 0 0 :=
  of_native_maps core0660 DegreeOneSmallSpectrum1387.graph DegreeOneSmallSpectrum1342.graph
    sourceMap0660 fusedMap0660 sourceMap0660_checked fusedMap0660_checked
    DegreeTwoThreeFiniteComparisons.comparison0660
#print axioms sourceMap0660_checked
#print axioms fusedMap0660_checked
#print axioms certified0660
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
