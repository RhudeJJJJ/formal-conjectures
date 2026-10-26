/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3837 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap3837 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3837 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3837_checked : acceptsGraphIso
    (source (graph core3837) (root 8) 1 4) DegreeTwoThreeSpectrum4384.graph sourceMap3837=true := by decide +kernel
theorem fusedMap3837_checked : acceptsGraphIso
    (fused (graph core3837) (root 8) 1 4) DegreeTwoThreeSpectrum3968.graph fusedMap3837=true := by decide +kernel
theorem certified3837 : Certified (graph core3837) (root 8) 1 4 :=
  of_native_maps core3837 DegreeTwoThreeSpectrum4384.graph DegreeTwoThreeSpectrum3968.graph
    sourceMap3837 fusedMap3837 sourceMap3837_checked fusedMap3837_checked
    DegreeTwoThreeFiniteComparisons.comparison3837
#print axioms sourceMap3837_checked
#print axioms fusedMap3837_checked
#print axioms certified3837
def sourceMap3837swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3837swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3837swap_checked : acceptsGraphIso
    (source (graph core3837) (root 8) 4 1) DegreeTwoThreeSpectrum4384.graph sourceMap3837swap=true := by decide +kernel
theorem fusedMap3837swap_checked : acceptsGraphIso
    (fused (graph core3837) (root 8) 4 1) DegreeTwoThreeSpectrum3968.graph fusedMap3837swap=true := by decide +kernel
theorem certified3837swap : Certified (graph core3837) (root 8) 4 1 :=
  of_native_maps core3837 DegreeTwoThreeSpectrum4384.graph DegreeTwoThreeSpectrum3968.graph
    sourceMap3837swap fusedMap3837swap sourceMap3837swap_checked fusedMap3837swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3837
#print axioms sourceMap3837swap_checked
#print axioms fusedMap3837swap_checked
#print axioms certified3837swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
