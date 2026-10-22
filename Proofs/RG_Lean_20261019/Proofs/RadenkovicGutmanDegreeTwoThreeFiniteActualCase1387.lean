/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1387 : Family 9 := level9.get ⟨570,by decide⟩
def sourceMap1387 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1387 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1387_checked : acceptsGraphIso
    (source (graph core1387) (root 9) 0 2) DegreeTwoThreeSpectrum2258.graph sourceMap1387=true := by decide +kernel
theorem fusedMap1387_checked : acceptsGraphIso
    (fused (graph core1387) (root 9) 0 2) DegreeTwoThreeSpectrum1957.graph fusedMap1387=true := by decide +kernel
theorem certified1387 : Certified (graph core1387) (root 9) 0 2 :=
  of_native_maps core1387 DegreeTwoThreeSpectrum2258.graph DegreeTwoThreeSpectrum1957.graph
    sourceMap1387 fusedMap1387 sourceMap1387_checked fusedMap1387_checked
    DegreeTwoThreeFiniteComparisons.comparison1387
#print axioms sourceMap1387_checked
#print axioms fusedMap1387_checked
#print axioms certified1387
def sourceMap1387swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1387swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1387swap_checked : acceptsGraphIso
    (source (graph core1387) (root 9) 2 0) DegreeTwoThreeSpectrum2258.graph sourceMap1387swap=true := by decide +kernel
theorem fusedMap1387swap_checked : acceptsGraphIso
    (fused (graph core1387) (root 9) 2 0) DegreeTwoThreeSpectrum1957.graph fusedMap1387swap=true := by decide +kernel
theorem certified1387swap : Certified (graph core1387) (root 9) 2 0 :=
  of_native_maps core1387 DegreeTwoThreeSpectrum2258.graph DegreeTwoThreeSpectrum1957.graph
    sourceMap1387swap fusedMap1387swap sourceMap1387swap_checked fusedMap1387swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1387
#print axioms sourceMap1387swap_checked
#print axioms fusedMap1387swap_checked
#print axioms certified1387swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
