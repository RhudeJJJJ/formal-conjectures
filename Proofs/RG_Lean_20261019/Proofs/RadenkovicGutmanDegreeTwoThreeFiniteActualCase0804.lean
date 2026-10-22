/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0804 : Family 10 := level10.get ⟨1216,by decide⟩
def sourceMap0804 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0804 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0804_checked : acceptsGraphIso
    (source (graph core0804) (root 10) 0 0) DegreeOneSmallSpectrum1650.graph sourceMap0804=true := by decide +kernel
theorem fusedMap0804_checked : acceptsGraphIso
    (fused (graph core0804) (root 10) 0 0) DegreeOneSmallSpectrum1633.graph fusedMap0804=true := by decide +kernel
theorem certified0804 : Certified (graph core0804) (root 10) 0 0 :=
  of_native_maps core0804 DegreeOneSmallSpectrum1650.graph DegreeOneSmallSpectrum1633.graph
    sourceMap0804 fusedMap0804 sourceMap0804_checked fusedMap0804_checked
    DegreeTwoThreeFiniteComparisons.comparison0804
#print axioms sourceMap0804_checked
#print axioms fusedMap0804_checked
#print axioms certified0804
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
