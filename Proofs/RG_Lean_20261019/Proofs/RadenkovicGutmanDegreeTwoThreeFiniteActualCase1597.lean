/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1597 : Family 10 := level10.get ⟨597,by decide⟩
def sourceMap1597 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1597 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1597_checked : acceptsGraphIso
    (source (graph core1597) (root 10) 0 2) DegreeTwoThreeSpectrum3257.graph sourceMap1597=true := by decide +kernel
theorem fusedMap1597_checked : acceptsGraphIso
    (fused (graph core1597) (root 10) 0 2) DegreeTwoThreeSpectrum2537.graph fusedMap1597=true := by decide +kernel
theorem certified1597 : Certified (graph core1597) (root 10) 0 2 :=
  of_native_maps core1597 DegreeTwoThreeSpectrum3257.graph DegreeTwoThreeSpectrum2537.graph
    sourceMap1597 fusedMap1597 sourceMap1597_checked fusedMap1597_checked
    DegreeTwoThreeFiniteComparisons.comparison1597
#print axioms sourceMap1597_checked
#print axioms fusedMap1597_checked
#print axioms certified1597
def sourceMap1597swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1597swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1597swap_checked : acceptsGraphIso
    (source (graph core1597) (root 10) 2 0) DegreeTwoThreeSpectrum3257.graph sourceMap1597swap=true := by decide +kernel
theorem fusedMap1597swap_checked : acceptsGraphIso
    (fused (graph core1597) (root 10) 2 0) DegreeTwoThreeSpectrum2537.graph fusedMap1597swap=true := by decide +kernel
theorem certified1597swap : Certified (graph core1597) (root 10) 2 0 :=
  of_native_maps core1597 DegreeTwoThreeSpectrum3257.graph DegreeTwoThreeSpectrum2537.graph
    sourceMap1597swap fusedMap1597swap sourceMap1597swap_checked fusedMap1597swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1597
#print axioms sourceMap1597swap_checked
#print axioms fusedMap1597swap_checked
#print axioms certified1597swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
