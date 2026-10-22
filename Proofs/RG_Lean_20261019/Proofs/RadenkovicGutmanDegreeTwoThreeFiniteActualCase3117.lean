/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3117 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap3117 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3117 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3117_checked : acceptsGraphIso
    (source (graph core3117) (root 7) 0 5) DegreeTwoThreeSpectrum2861.graph sourceMap3117=true := by decide +kernel
theorem fusedMap3117_checked : acceptsGraphIso
    (fused (graph core3117) (root 7) 0 5) DegreeTwoThreeSpectrum2384.graph fusedMap3117=true := by decide +kernel
theorem certified3117 : Certified (graph core3117) (root 7) 0 5 :=
  of_native_maps core3117 DegreeTwoThreeSpectrum2861.graph DegreeTwoThreeSpectrum2384.graph
    sourceMap3117 fusedMap3117 sourceMap3117_checked fusedMap3117_checked
    DegreeTwoThreeFiniteComparisons.comparison3117
#print axioms sourceMap3117_checked
#print axioms fusedMap3117_checked
#print axioms certified3117
def sourceMap3117swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3117swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3117swap_checked : acceptsGraphIso
    (source (graph core3117) (root 7) 5 0) DegreeTwoThreeSpectrum2861.graph sourceMap3117swap=true := by decide +kernel
theorem fusedMap3117swap_checked : acceptsGraphIso
    (fused (graph core3117) (root 7) 5 0) DegreeTwoThreeSpectrum2384.graph fusedMap3117swap=true := by decide +kernel
theorem certified3117swap : Certified (graph core3117) (root 7) 5 0 :=
  of_native_maps core3117 DegreeTwoThreeSpectrum2861.graph DegreeTwoThreeSpectrum2384.graph
    sourceMap3117swap fusedMap3117swap sourceMap3117swap_checked fusedMap3117swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3117
#print axioms sourceMap3117swap_checked
#print axioms fusedMap3117swap_checked
#print axioms certified3117swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
