/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1374 : Family 9 := level9.get ⟨531,by decide⟩
def sourceMap1374 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1374 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 0 2 v)
theorem sourceMap1374_checked : acceptsGraphIso
    (source (graph core1374) (root 9) 0 2) DegreeTwoThreeSpectrum2125.graph sourceMap1374=true := by decide +kernel
theorem fusedMap1374_checked : acceptsGraphIso
    (fused (graph core1374) (root 9) 0 2) DegreeTwoThreeSpectrum2237.graph fusedMap1374=true := by decide +kernel
theorem certified1374 : Certified (graph core1374) (root 9) 0 2 :=
  of_native_maps core1374 DegreeTwoThreeSpectrum2125.graph DegreeTwoThreeSpectrum2237.graph
    sourceMap1374 fusedMap1374 sourceMap1374_checked fusedMap1374_checked
    DegreeTwoThreeFiniteComparisons.comparison1374
#print axioms sourceMap1374_checked
#print axioms fusedMap1374_checked
#print axioms certified1374
def sourceMap1374swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,10,11,12,13,1,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1374swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,5,6,7,8] (fusedLabel 9 2 0 v)
theorem sourceMap1374swap_checked : acceptsGraphIso
    (source (graph core1374) (root 9) 2 0) DegreeTwoThreeSpectrum2125.graph sourceMap1374swap=true := by decide +kernel
theorem fusedMap1374swap_checked : acceptsGraphIso
    (fused (graph core1374) (root 9) 2 0) DegreeTwoThreeSpectrum2237.graph fusedMap1374swap=true := by decide +kernel
theorem certified1374swap : Certified (graph core1374) (root 9) 2 0 :=
  of_native_maps core1374 DegreeTwoThreeSpectrum2125.graph DegreeTwoThreeSpectrum2237.graph
    sourceMap1374swap fusedMap1374swap sourceMap1374swap_checked fusedMap1374swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1374
#print axioms sourceMap1374swap_checked
#print axioms fusedMap1374swap_checked
#print axioms certified1374swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
