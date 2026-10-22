/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0529 : Family 10 := level10.get ⟨482,by decide⟩
def sourceMap0529 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0529 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0529_checked : acceptsGraphIso
    (source (graph core0529) (root 10) 0 0) DegreeOneSmallSpectrum1374.graph sourceMap0529=true := by decide +kernel
theorem fusedMap0529_checked : acceptsGraphIso
    (fused (graph core0529) (root 10) 0 0) DegreeOneSmallSpectrum1323.graph fusedMap0529=true := by decide +kernel
theorem certified0529 : Certified (graph core0529) (root 10) 0 0 :=
  of_native_maps core0529 DegreeOneSmallSpectrum1374.graph DegreeOneSmallSpectrum1323.graph
    sourceMap0529 fusedMap0529 sourceMap0529_checked fusedMap0529_checked
    DegreeTwoThreeFiniteComparisons.comparison0529
#print axioms sourceMap0529_checked
#print axioms fusedMap0529_checked
#print axioms certified0529
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
