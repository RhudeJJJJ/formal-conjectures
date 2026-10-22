/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1474 : Family 10 := level10.get ⟨194,by decide⟩
def sourceMap1474 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1474 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1474_checked : acceptsGraphIso
    (source (graph core1474) (root 10) 0 2) DegreeTwoThreeSpectrum2452.graph sourceMap1474=true := by decide +kernel
theorem fusedMap1474_checked : acceptsGraphIso
    (fused (graph core1474) (root 10) 0 2) DegreeTwoThreeSpectrum2454.graph fusedMap1474=true := by decide +kernel
theorem certified1474 : Certified (graph core1474) (root 10) 0 2 :=
  of_native_maps core1474 DegreeTwoThreeSpectrum2452.graph DegreeTwoThreeSpectrum2454.graph
    sourceMap1474 fusedMap1474 sourceMap1474_checked fusedMap1474_checked
    DegreeTwoThreeFiniteComparisons.comparison1474
#print axioms sourceMap1474_checked
#print axioms fusedMap1474_checked
#print axioms certified1474
def sourceMap1474swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1474swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1474swap_checked : acceptsGraphIso
    (source (graph core1474) (root 10) 2 0) DegreeTwoThreeSpectrum2452.graph sourceMap1474swap=true := by decide +kernel
theorem fusedMap1474swap_checked : acceptsGraphIso
    (fused (graph core1474) (root 10) 2 0) DegreeTwoThreeSpectrum2454.graph fusedMap1474swap=true := by decide +kernel
theorem certified1474swap : Certified (graph core1474) (root 10) 2 0 :=
  of_native_maps core1474 DegreeTwoThreeSpectrum2452.graph DegreeTwoThreeSpectrum2454.graph
    sourceMap1474swap fusedMap1474swap sourceMap1474swap_checked fusedMap1474swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1474
#print axioms sourceMap1474swap_checked
#print axioms fusedMap1474swap_checked
#print axioms certified1474swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
