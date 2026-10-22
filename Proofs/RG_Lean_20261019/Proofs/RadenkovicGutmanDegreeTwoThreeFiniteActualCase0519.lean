/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0519 : Family 10 := level10.get ⟨458,by decide⟩
def sourceMap0519 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,8,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0519 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0519_checked : acceptsGraphIso
    (source (graph core0519) (root 10) 0 0) DegreeOneSmallSpectrum1011.graph sourceMap0519=true := by decide +kernel
theorem fusedMap0519_checked : acceptsGraphIso
    (fused (graph core0519) (root 10) 0 0) DegreeOneSmallSpectrum1414.graph fusedMap0519=true := by decide +kernel
theorem certified0519 : Certified (graph core0519) (root 10) 0 0 :=
  of_native_maps core0519 DegreeOneSmallSpectrum1011.graph DegreeOneSmallSpectrum1414.graph
    sourceMap0519 fusedMap0519 sourceMap0519_checked fusedMap0519_checked
    DegreeTwoThreeFiniteComparisons.comparison0519
#print axioms sourceMap0519_checked
#print axioms fusedMap0519_checked
#print axioms certified0519
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
