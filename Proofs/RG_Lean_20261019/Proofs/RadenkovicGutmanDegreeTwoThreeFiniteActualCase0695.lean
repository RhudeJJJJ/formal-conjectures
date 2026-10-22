/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0695 : Family 10 := level10.get ⟨951,by decide⟩
def sourceMap0695 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,6,7,8,9,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0695 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0695_checked : acceptsGraphIso
    (source (graph core0695) (root 10) 0 0) DegreeOneSmallSpectrum1624.graph sourceMap0695=true := by decide +kernel
theorem fusedMap0695_checked : acceptsGraphIso
    (fused (graph core0695) (root 10) 0 0) DegreeOneSmallSpectrum1405.graph fusedMap0695=true := by decide +kernel
theorem certified0695 : Certified (graph core0695) (root 10) 0 0 :=
  of_native_maps core0695 DegreeOneSmallSpectrum1624.graph DegreeOneSmallSpectrum1405.graph
    sourceMap0695 fusedMap0695 sourceMap0695_checked fusedMap0695_checked
    DegreeTwoThreeFiniteComparisons.comparison0695
#print axioms sourceMap0695_checked
#print axioms fusedMap0695_checked
#print axioms certified0695
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
