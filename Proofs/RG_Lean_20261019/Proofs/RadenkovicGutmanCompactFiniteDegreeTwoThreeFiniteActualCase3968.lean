/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3968 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap3968 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3968 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3968_checked : acceptsGraphIso
    (source (graph core3968) (root 7) 1 5) DegreeTwoThreeSpectrum4649.graph sourceMap3968=true := by decide +kernel
theorem fusedMap3968_checked : acceptsGraphIso
    (fused (graph core3968) (root 7) 1 5) DegreeTwoThreeSpectrum4124.graph fusedMap3968=true := by decide +kernel
theorem certified3968 : Certified (graph core3968) (root 7) 1 5 :=
  of_native_maps core3968 DegreeTwoThreeSpectrum4649.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap3968 fusedMap3968 sourceMap3968_checked fusedMap3968_checked
    DegreeTwoThreeFiniteComparisons.comparison3968
#print axioms sourceMap3968_checked
#print axioms fusedMap3968_checked
#print axioms certified3968
def sourceMap3968swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3968swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3968swap_checked : acceptsGraphIso
    (source (graph core3968) (root 7) 5 1) DegreeTwoThreeSpectrum4649.graph sourceMap3968swap=true := by decide +kernel
theorem fusedMap3968swap_checked : acceptsGraphIso
    (fused (graph core3968) (root 7) 5 1) DegreeTwoThreeSpectrum4124.graph fusedMap3968swap=true := by decide +kernel
theorem certified3968swap : Certified (graph core3968) (root 7) 5 1 :=
  of_native_maps core3968 DegreeTwoThreeSpectrum4649.graph DegreeTwoThreeSpectrum4124.graph
    sourceMap3968swap fusedMap3968swap sourceMap3968swap_checked fusedMap3968swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3968
#print axioms sourceMap3968swap_checked
#print axioms fusedMap3968swap_checked
#print axioms certified3968swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
