/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0652 : Family 10 := level10.get ⟨837,by decide⟩
def sourceMap0652 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0652 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0652_checked : acceptsGraphIso
    (source (graph core0652) (root 10) 0 0) DegreeOneSmallSpectrum1385.graph sourceMap0652=true := by decide +kernel
theorem fusedMap0652_checked : acceptsGraphIso
    (fused (graph core0652) (root 10) 0 0) DegreeOneSmallSpectrum1340.graph fusedMap0652=true := by decide +kernel
theorem certified0652 : Certified (graph core0652) (root 10) 0 0 :=
  of_native_maps core0652 DegreeOneSmallSpectrum1385.graph DegreeOneSmallSpectrum1340.graph
    sourceMap0652 fusedMap0652 sourceMap0652_checked fusedMap0652_checked
    DegreeTwoThreeFiniteComparisons.comparison0652
#print axioms sourceMap0652_checked
#print axioms fusedMap0652_checked
#print axioms certified0652
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
