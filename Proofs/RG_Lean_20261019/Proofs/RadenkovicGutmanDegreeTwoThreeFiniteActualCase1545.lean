/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1545 : Family 10 := level10.get ⟨441,by decide⟩
def sourceMap1545 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1545 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1545_checked : acceptsGraphIso
    (source (graph core1545) (root 10) 0 2) DegreeTwoThreeSpectrum2903.graph sourceMap1545=true := by decide +kernel
theorem fusedMap1545_checked : acceptsGraphIso
    (fused (graph core1545) (root 10) 0 2) DegreeTwoThreeSpectrum2976.graph fusedMap1545=true := by decide +kernel
theorem certified1545 : Certified (graph core1545) (root 10) 0 2 :=
  of_native_maps core1545 DegreeTwoThreeSpectrum2903.graph DegreeTwoThreeSpectrum2976.graph
    sourceMap1545 fusedMap1545 sourceMap1545_checked fusedMap1545_checked
    DegreeTwoThreeFiniteComparisons.comparison1545
#print axioms sourceMap1545_checked
#print axioms fusedMap1545_checked
#print axioms certified1545
def sourceMap1545swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1545swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1545swap_checked : acceptsGraphIso
    (source (graph core1545) (root 10) 2 0) DegreeTwoThreeSpectrum2903.graph sourceMap1545swap=true := by decide +kernel
theorem fusedMap1545swap_checked : acceptsGraphIso
    (fused (graph core1545) (root 10) 2 0) DegreeTwoThreeSpectrum2976.graph fusedMap1545swap=true := by decide +kernel
theorem certified1545swap : Certified (graph core1545) (root 10) 2 0 :=
  of_native_maps core1545 DegreeTwoThreeSpectrum2903.graph DegreeTwoThreeSpectrum2976.graph
    sourceMap1545swap fusedMap1545swap sourceMap1545swap_checked fusedMap1545swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1545
#print axioms sourceMap1545swap_checked
#print axioms fusedMap1545swap_checked
#print axioms certified1545swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
