/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3993 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap3993 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,7,8,1,0,10,11,12,13,14] (sourceLabel 5 1 6 v)
def fusedMap3993 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 1 6 v)
theorem sourceMap3993_checked : acceptsGraphIso
    (source (graph core3993) (root 5) 1 6) DegreeTwoThreeSpectrum2572.graph sourceMap3993=true := by decide +kernel
theorem fusedMap3993_checked : acceptsGraphIso
    (fused (graph core3993) (root 5) 1 6) DegreeTwoThreeSpectrum2333.graph fusedMap3993=true := by decide +kernel
theorem certified3993 : Certified (graph core3993) (root 5) 1 6 :=
  of_native_maps core3993 DegreeTwoThreeSpectrum2572.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap3993 fusedMap3993 sourceMap3993_checked fusedMap3993_checked
    DegreeTwoThreeFiniteComparisons.comparison3993
#print axioms sourceMap3993_checked
#print axioms fusedMap3993_checked
#print axioms certified3993
def sourceMap3993swap : (Vertices 5 ⊕ Fin 7 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,9,1,0,10,11,12,13,14,7,8] (sourceLabel 5 6 1 v)
def fusedMap3993swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 6 1 v)
theorem sourceMap3993swap_checked : acceptsGraphIso
    (source (graph core3993) (root 5) 6 1) DegreeTwoThreeSpectrum2572.graph sourceMap3993swap=true := by decide +kernel
theorem fusedMap3993swap_checked : acceptsGraphIso
    (fused (graph core3993) (root 5) 6 1) DegreeTwoThreeSpectrum2333.graph fusedMap3993swap=true := by decide +kernel
theorem certified3993swap : Certified (graph core3993) (root 5) 6 1 :=
  of_native_maps core3993 DegreeTwoThreeSpectrum2572.graph DegreeTwoThreeSpectrum2333.graph
    sourceMap3993swap fusedMap3993swap sourceMap3993swap_checked fusedMap3993swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3993
#print axioms sourceMap3993swap_checked
#print axioms fusedMap3993swap_checked
#print axioms certified3993swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
