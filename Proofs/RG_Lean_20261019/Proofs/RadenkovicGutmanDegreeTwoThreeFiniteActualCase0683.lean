/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0683 : Family 10 := level10.get ⟨917,by decide⟩
def sourceMap0683 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0683 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0683_checked : acceptsGraphIso
    (source (graph core0683) (root 10) 0 0) DegreeOneSmallSpectrum1225.graph sourceMap0683=true := by decide +kernel
theorem fusedMap0683_checked : acceptsGraphIso
    (fused (graph core0683) (root 10) 0 0) DegreeOneSmallSpectrum1210.graph fusedMap0683=true := by decide +kernel
theorem certified0683 : Certified (graph core0683) (root 10) 0 0 :=
  of_native_maps core0683 DegreeOneSmallSpectrum1225.graph DegreeOneSmallSpectrum1210.graph
    sourceMap0683 fusedMap0683 sourceMap0683_checked fusedMap0683_checked
    DegreeTwoThreeFiniteComparisons.comparison0683
#print axioms sourceMap0683_checked
#print axioms fusedMap0683_checked
#print axioms certified0683
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
