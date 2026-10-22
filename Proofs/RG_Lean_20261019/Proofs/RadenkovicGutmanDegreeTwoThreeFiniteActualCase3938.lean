/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3938 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3938 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3938 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3938_checked : acceptsGraphIso
    (source (graph core3938) (root 6) 1 5) DegreeTwoThreeSpectrum2973.graph sourceMap3938=true := by decide +kernel
theorem fusedMap3938_checked : acceptsGraphIso
    (fused (graph core3938) (root 6) 1 5) DegreeTwoThreeSpectrum2414.graph fusedMap3938=true := by decide +kernel
theorem certified3938 : Certified (graph core3938) (root 6) 1 5 :=
  of_native_maps core3938 DegreeTwoThreeSpectrum2973.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap3938 fusedMap3938 sourceMap3938_checked fusedMap3938_checked
    DegreeTwoThreeFiniteComparisons.comparison3938
#print axioms sourceMap3938_checked
#print axioms fusedMap3938_checked
#print axioms certified3938
def sourceMap3938swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3938swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3938swap_checked : acceptsGraphIso
    (source (graph core3938) (root 6) 5 1) DegreeTwoThreeSpectrum2973.graph sourceMap3938swap=true := by decide +kernel
theorem fusedMap3938swap_checked : acceptsGraphIso
    (fused (graph core3938) (root 6) 5 1) DegreeTwoThreeSpectrum2414.graph fusedMap3938swap=true := by decide +kernel
theorem certified3938swap : Certified (graph core3938) (root 6) 5 1 :=
  of_native_maps core3938 DegreeTwoThreeSpectrum2973.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap3938swap fusedMap3938swap sourceMap3938swap_checked fusedMap3938swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3938
#print axioms sourceMap3938swap_checked
#print axioms fusedMap3938swap_checked
#print axioms certified3938swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
