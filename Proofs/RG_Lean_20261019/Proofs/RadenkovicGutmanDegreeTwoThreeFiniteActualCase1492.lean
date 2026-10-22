/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1492 : Family 10 := level10.get ⟨266,by decide⟩
def sourceMap1492 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1492 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1492_checked : acceptsGraphIso
    (source (graph core1492) (root 10) 0 2) DegreeTwoThreeSpectrum2616.graph sourceMap1492=true := by decide +kernel
theorem fusedMap1492_checked : acceptsGraphIso
    (fused (graph core1492) (root 10) 0 2) DegreeTwoThreeSpectrum2618.graph fusedMap1492=true := by decide +kernel
theorem certified1492 : Certified (graph core1492) (root 10) 0 2 :=
  of_native_maps core1492 DegreeTwoThreeSpectrum2616.graph DegreeTwoThreeSpectrum2618.graph
    sourceMap1492 fusedMap1492 sourceMap1492_checked fusedMap1492_checked
    DegreeTwoThreeFiniteComparisons.comparison1492
#print axioms sourceMap1492_checked
#print axioms fusedMap1492_checked
#print axioms certified1492
def sourceMap1492swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1492swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1492swap_checked : acceptsGraphIso
    (source (graph core1492) (root 10) 2 0) DegreeTwoThreeSpectrum2616.graph sourceMap1492swap=true := by decide +kernel
theorem fusedMap1492swap_checked : acceptsGraphIso
    (fused (graph core1492) (root 10) 2 0) DegreeTwoThreeSpectrum2618.graph fusedMap1492swap=true := by decide +kernel
theorem certified1492swap : Certified (graph core1492) (root 10) 2 0 :=
  of_native_maps core1492 DegreeTwoThreeSpectrum2616.graph DegreeTwoThreeSpectrum2618.graph
    sourceMap1492swap fusedMap1492swap sourceMap1492swap_checked fusedMap1492swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1492
#print axioms sourceMap1492swap_checked
#print axioms fusedMap1492swap_checked
#print axioms certified1492swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
