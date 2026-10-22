/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0701 : Family 10 := level10.get ⟨962,by decide⟩
def sourceMap0701 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0701 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0701_checked : acceptsGraphIso
    (source (graph core0701) (root 10) 0 0) DegreeOneSmallSpectrum1501.graph sourceMap0701=true := by decide +kernel
theorem fusedMap0701_checked : acceptsGraphIso
    (fused (graph core0701) (root 10) 0 0) DegreeOneSmallSpectrum1491.graph fusedMap0701=true := by decide +kernel
theorem certified0701 : Certified (graph core0701) (root 10) 0 0 :=
  of_native_maps core0701 DegreeOneSmallSpectrum1501.graph DegreeOneSmallSpectrum1491.graph
    sourceMap0701 fusedMap0701 sourceMap0701_checked fusedMap0701_checked
    DegreeTwoThreeFiniteComparisons.comparison0701
#print axioms sourceMap0701_checked
#print axioms fusedMap0701_checked
#print axioms certified0701
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
