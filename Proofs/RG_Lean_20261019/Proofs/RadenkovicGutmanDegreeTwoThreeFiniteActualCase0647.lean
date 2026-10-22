/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0647 : Family 10 := level10.get ⟨822,by decide⟩
def sourceMap0647 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0647 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0647_checked : acceptsGraphIso
    (source (graph core0647) (root 10) 0 0) DegreeOneSmallSpectrum1222.graph sourceMap0647=true := by decide +kernel
theorem fusedMap0647_checked : acceptsGraphIso
    (fused (graph core0647) (root 10) 0 0) DegreeOneSmallSpectrum1207.graph fusedMap0647=true := by decide +kernel
theorem certified0647 : Certified (graph core0647) (root 10) 0 0 :=
  of_native_maps core0647 DegreeOneSmallSpectrum1222.graph DegreeOneSmallSpectrum1207.graph
    sourceMap0647 fusedMap0647 sourceMap0647_checked fusedMap0647_checked
    DegreeTwoThreeFiniteComparisons.comparison0647
#print axioms sourceMap0647_checked
#print axioms fusedMap0647_checked
#print axioms certified0647
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
