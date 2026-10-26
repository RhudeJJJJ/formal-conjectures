/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3765 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3765 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,7,5,6,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap3765 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap3765_checked : acceptsGraphIso
    (source (graph core3765) (root 4) 1 4) DegreeOneSmallSpectrum571.graph sourceMap3765=true := by decide +kernel
theorem fusedMap3765_checked : acceptsGraphIso
    (fused (graph core3765) (root 4) 1 4) DegreeOneSmallSpectrum392.graph fusedMap3765=true := by decide +kernel
theorem certified3765 : Certified (graph core3765) (root 4) 1 4 :=
  of_native_maps core3765 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum392.graph
    sourceMap3765 fusedMap3765 sourceMap3765_checked fusedMap3765_checked
    DegreeTwoThreeFiniteComparisons.comparison3765
#print axioms sourceMap3765_checked
#print axioms fusedMap3765_checked
#print axioms certified3765
def sourceMap3765swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,7,0,8,9,10,11,5,6] (sourceLabel 4 4 1 v)
def fusedMap3765swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap3765swap_checked : acceptsGraphIso
    (source (graph core3765) (root 4) 4 1) DegreeOneSmallSpectrum571.graph sourceMap3765swap=true := by decide +kernel
theorem fusedMap3765swap_checked : acceptsGraphIso
    (fused (graph core3765) (root 4) 4 1) DegreeOneSmallSpectrum392.graph fusedMap3765swap=true := by decide +kernel
theorem certified3765swap : Certified (graph core3765) (root 4) 4 1 :=
  of_native_maps core3765 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum392.graph
    sourceMap3765swap fusedMap3765swap sourceMap3765swap_checked fusedMap3765swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3765
#print axioms sourceMap3765swap_checked
#print axioms fusedMap3765swap_checked
#print axioms certified3765swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
