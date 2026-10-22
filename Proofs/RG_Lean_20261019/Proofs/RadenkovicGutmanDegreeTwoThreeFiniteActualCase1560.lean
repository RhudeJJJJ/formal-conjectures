/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1560 : Family 10 := level10.get ⟨481,by decide⟩
def sourceMap1560 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1560 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1560_checked : acceptsGraphIso
    (source (graph core1560) (root 10) 0 2) DegreeTwoThreeSpectrum2885.graph sourceMap1560=true := by decide +kernel
theorem fusedMap1560_checked : acceptsGraphIso
    (fused (graph core1560) (root 10) 0 2) DegreeTwoThreeSpectrum2992.graph fusedMap1560=true := by decide +kernel
theorem certified1560 : Certified (graph core1560) (root 10) 0 2 :=
  of_native_maps core1560 DegreeTwoThreeSpectrum2885.graph DegreeTwoThreeSpectrum2992.graph
    sourceMap1560 fusedMap1560 sourceMap1560_checked fusedMap1560_checked
    DegreeTwoThreeFiniteComparisons.comparison1560
#print axioms sourceMap1560_checked
#print axioms fusedMap1560_checked
#print axioms certified1560
def sourceMap1560swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1560swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1560swap_checked : acceptsGraphIso
    (source (graph core1560) (root 10) 2 0) DegreeTwoThreeSpectrum2885.graph sourceMap1560swap=true := by decide +kernel
theorem fusedMap1560swap_checked : acceptsGraphIso
    (fused (graph core1560) (root 10) 2 0) DegreeTwoThreeSpectrum2992.graph fusedMap1560swap=true := by decide +kernel
theorem certified1560swap : Certified (graph core1560) (root 10) 2 0 :=
  of_native_maps core1560 DegreeTwoThreeSpectrum2885.graph DegreeTwoThreeSpectrum2992.graph
    sourceMap1560swap fusedMap1560swap sourceMap1560swap_checked fusedMap1560swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1560
#print axioms sourceMap1560swap_checked
#print axioms fusedMap1560swap_checked
#print axioms certified1560swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
