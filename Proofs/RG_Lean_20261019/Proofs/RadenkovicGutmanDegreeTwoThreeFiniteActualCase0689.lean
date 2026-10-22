/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0689 : Family 10 := level10.get ⟨937,by decide⟩
def sourceMap0689 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,9,10,11,12,1,2,3,8,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0689 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0689_checked : acceptsGraphIso
    (source (graph core0689) (root 10) 0 0) DegreeOneSmallSpectrum1465.graph sourceMap0689=true := by decide +kernel
theorem fusedMap0689_checked : acceptsGraphIso
    (fused (graph core0689) (root 10) 0 0) DegreeOneSmallSpectrum1395.graph fusedMap0689=true := by decide +kernel
theorem certified0689 : Certified (graph core0689) (root 10) 0 0 :=
  of_native_maps core0689 DegreeOneSmallSpectrum1465.graph DegreeOneSmallSpectrum1395.graph
    sourceMap0689 fusedMap0689 sourceMap0689_checked fusedMap0689_checked
    DegreeTwoThreeFiniteComparisons.comparison0689
#print axioms sourceMap0689_checked
#print axioms fusedMap0689_checked
#print axioms certified0689
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
