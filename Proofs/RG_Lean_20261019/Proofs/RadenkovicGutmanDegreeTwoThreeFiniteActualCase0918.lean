/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0918 : Family 10 := level10.get ⟨1485,by decide⟩
def sourceMap0918 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0918 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,2,3,4,5,6,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0918_checked : acceptsGraphIso
    (source (graph core0918) (root 10) 0 0) DegreeOneSmallSpectrum1577.graph sourceMap0918=true := by decide +kernel
theorem fusedMap0918_checked : acceptsGraphIso
    (fused (graph core0918) (root 10) 0 0) DegreeOneSmallSpectrum1568.graph fusedMap0918=true := by decide +kernel
theorem certified0918 : Certified (graph core0918) (root 10) 0 0 :=
  of_native_maps core0918 DegreeOneSmallSpectrum1577.graph DegreeOneSmallSpectrum1568.graph
    sourceMap0918 fusedMap0918 sourceMap0918_checked fusedMap0918_checked
    DegreeTwoThreeFiniteComparisons.comparison0918
#print axioms sourceMap0918_checked
#print axioms fusedMap0918_checked
#print axioms certified0918
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
