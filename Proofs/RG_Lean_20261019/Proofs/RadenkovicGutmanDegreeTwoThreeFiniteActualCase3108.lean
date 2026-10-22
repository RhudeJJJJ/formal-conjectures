/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3108 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap3108 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3108 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3108_checked : acceptsGraphIso
    (source (graph core3108) (root 7) 0 5) DegreeTwoThreeSpectrum2430.graph sourceMap3108=true := by decide +kernel
theorem fusedMap3108_checked : acceptsGraphIso
    (fused (graph core3108) (root 7) 0 5) DegreeTwoThreeSpectrum2431.graph fusedMap3108=true := by decide +kernel
theorem certified3108 : Certified (graph core3108) (root 7) 0 5 :=
  of_native_maps core3108 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2431.graph
    sourceMap3108 fusedMap3108 sourceMap3108_checked fusedMap3108_checked
    DegreeTwoThreeFiniteComparisons.comparison3108
#print axioms sourceMap3108_checked
#print axioms fusedMap3108_checked
#print axioms certified3108
def sourceMap3108swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,8] (sourceLabel 7 5 0 v)
def fusedMap3108swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3108swap_checked : acceptsGraphIso
    (source (graph core3108) (root 7) 5 0) DegreeTwoThreeSpectrum2430.graph sourceMap3108swap=true := by decide +kernel
theorem fusedMap3108swap_checked : acceptsGraphIso
    (fused (graph core3108) (root 7) 5 0) DegreeTwoThreeSpectrum2431.graph fusedMap3108swap=true := by decide +kernel
theorem certified3108swap : Certified (graph core3108) (root 7) 5 0 :=
  of_native_maps core3108 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2431.graph
    sourceMap3108swap fusedMap3108swap sourceMap3108swap_checked fusedMap3108swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3108
#print axioms sourceMap3108swap_checked
#print axioms fusedMap3108swap_checked
#print axioms certified3108swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
