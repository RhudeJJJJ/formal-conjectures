/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3078 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3078 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap3078 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap3078_checked : acceptsGraphIso
    (source (graph core3078) (root 4) 0 5) DegreeOneSmallSpectrum388.graph sourceMap3078=true := by decide +kernel
theorem fusedMap3078_checked : acceptsGraphIso
    (fused (graph core3078) (root 4) 0 5) DegreeOneSmallSpectrum392.graph fusedMap3078=true := by decide +kernel
theorem certified3078 : Certified (graph core3078) (root 4) 0 5 :=
  of_native_maps core3078 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum392.graph
    sourceMap3078 fusedMap3078 sourceMap3078_checked fusedMap3078_checked
    DegreeTwoThreeFiniteComparisons.comparison3078
#print axioms sourceMap3078_checked
#print axioms fusedMap3078_checked
#print axioms certified3078
def sourceMap3078swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,11,6] (sourceLabel 4 5 0 v)
def fusedMap3078swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap3078swap_checked : acceptsGraphIso
    (source (graph core3078) (root 4) 5 0) DegreeOneSmallSpectrum388.graph sourceMap3078swap=true := by decide +kernel
theorem fusedMap3078swap_checked : acceptsGraphIso
    (fused (graph core3078) (root 4) 5 0) DegreeOneSmallSpectrum392.graph fusedMap3078swap=true := by decide +kernel
theorem certified3078swap : Certified (graph core3078) (root 4) 5 0 :=
  of_native_maps core3078 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum392.graph
    sourceMap3078swap fusedMap3078swap sourceMap3078swap_checked fusedMap3078swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3078
#print axioms sourceMap3078swap_checked
#print axioms fusedMap3078swap_checked
#print axioms certified3078swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
