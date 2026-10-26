/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3767 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3767 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap3767 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap3767_checked : acceptsGraphIso
    (source (graph core3767) (root 4) 1 4) DegreeOneSmallSpectrum500.graph sourceMap3767=true := by decide +kernel
theorem fusedMap3767_checked : acceptsGraphIso
    (fused (graph core3767) (root 4) 1 4) DegreeOneSmallSpectrum379.graph fusedMap3767=true := by decide +kernel
theorem certified3767 : Certified (graph core3767) (root 4) 1 4 :=
  of_native_maps core3767 DegreeOneSmallSpectrum500.graph DegreeOneSmallSpectrum379.graph
    sourceMap3767 fusedMap3767 sourceMap3767_checked fusedMap3767_checked
    DegreeTwoThreeFiniteComparisons.comparison3767
#print axioms sourceMap3767_checked
#print axioms fusedMap3767_checked
#print axioms certified3767
def sourceMap3767swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,6,7] (sourceLabel 4 4 1 v)
def fusedMap3767swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap3767swap_checked : acceptsGraphIso
    (source (graph core3767) (root 4) 4 1) DegreeOneSmallSpectrum500.graph sourceMap3767swap=true := by decide +kernel
theorem fusedMap3767swap_checked : acceptsGraphIso
    (fused (graph core3767) (root 4) 4 1) DegreeOneSmallSpectrum379.graph fusedMap3767swap=true := by decide +kernel
theorem certified3767swap : Certified (graph core3767) (root 4) 4 1 :=
  of_native_maps core3767 DegreeOneSmallSpectrum500.graph DegreeOneSmallSpectrum379.graph
    sourceMap3767swap fusedMap3767swap sourceMap3767swap_checked fusedMap3767swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3767
#print axioms sourceMap3767swap_checked
#print axioms fusedMap3767swap_checked
#print axioms certified3767swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
