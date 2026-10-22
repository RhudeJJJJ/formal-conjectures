/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1682 : Family 10 := level10.get ⟨833,by decide⟩
def sourceMap1682 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1682 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1682_checked : acceptsGraphIso
    (source (graph core1682) (root 10) 0 2) DegreeTwoThreeSpectrum3626.graph sourceMap1682=true := by decide +kernel
theorem fusedMap1682_checked : acceptsGraphIso
    (fused (graph core1682) (root 10) 0 2) DegreeTwoThreeSpectrum2818.graph fusedMap1682=true := by decide +kernel
theorem certified1682 : Certified (graph core1682) (root 10) 0 2 :=
  of_native_maps core1682 DegreeTwoThreeSpectrum3626.graph DegreeTwoThreeSpectrum2818.graph
    sourceMap1682 fusedMap1682 sourceMap1682_checked fusedMap1682_checked
    DegreeTwoThreeFiniteComparisons.comparison1682
#print axioms sourceMap1682_checked
#print axioms fusedMap1682_checked
#print axioms certified1682
def sourceMap1682swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1682swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1682swap_checked : acceptsGraphIso
    (source (graph core1682) (root 10) 2 0) DegreeTwoThreeSpectrum3626.graph sourceMap1682swap=true := by decide +kernel
theorem fusedMap1682swap_checked : acceptsGraphIso
    (fused (graph core1682) (root 10) 2 0) DegreeTwoThreeSpectrum2818.graph fusedMap1682swap=true := by decide +kernel
theorem certified1682swap : Certified (graph core1682) (root 10) 2 0 :=
  of_native_maps core1682 DegreeTwoThreeSpectrum3626.graph DegreeTwoThreeSpectrum2818.graph
    sourceMap1682swap fusedMap1682swap sourceMap1682swap_checked fusedMap1682swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1682
#print axioms sourceMap1682swap_checked
#print axioms fusedMap1682swap_checked
#print axioms certified1682swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
