/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0513 : Family 10 := level10.get ⟨441,by decide⟩
def sourceMap0513 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0513 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0513_checked : acceptsGraphIso
    (source (graph core0513) (root 10) 0 0) DegreeOneSmallSpectrum1040.graph sourceMap0513=true := by decide +kernel
theorem fusedMap0513_checked : acceptsGraphIso
    (fused (graph core0513) (root 10) 0 0) DegreeOneSmallSpectrum1454.graph fusedMap0513=true := by decide +kernel
theorem certified0513 : Certified (graph core0513) (root 10) 0 0 :=
  of_native_maps core0513 DegreeOneSmallSpectrum1040.graph DegreeOneSmallSpectrum1454.graph
    sourceMap0513 fusedMap0513 sourceMap0513_checked fusedMap0513_checked
    DegreeTwoThreeFiniteComparisons.comparison0513
#print axioms sourceMap0513_checked
#print axioms fusedMap0513_checked
#print axioms certified0513
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
