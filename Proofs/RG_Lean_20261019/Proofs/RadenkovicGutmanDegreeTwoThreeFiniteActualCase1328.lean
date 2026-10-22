/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1328 : Family 9 := level9.get ⟨429,by decide⟩
def sourceMap1328 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1328 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1328_checked : acceptsGraphIso
    (source (graph core1328) (root 9) 0 2) DegreeTwoThreeSpectrum2099.graph sourceMap1328=true := by decide +kernel
theorem fusedMap1328_checked : acceptsGraphIso
    (fused (graph core1328) (root 9) 0 2) DegreeTwoThreeSpectrum2100.graph fusedMap1328=true := by decide +kernel
theorem certified1328 : Certified (graph core1328) (root 9) 0 2 :=
  of_native_maps core1328 DegreeTwoThreeSpectrum2099.graph DegreeTwoThreeSpectrum2100.graph
    sourceMap1328 fusedMap1328 sourceMap1328_checked fusedMap1328_checked
    DegreeTwoThreeFiniteComparisons.comparison1328
#print axioms sourceMap1328_checked
#print axioms fusedMap1328_checked
#print axioms certified1328
def sourceMap1328swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1328swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1328swap_checked : acceptsGraphIso
    (source (graph core1328) (root 9) 2 0) DegreeTwoThreeSpectrum2099.graph sourceMap1328swap=true := by decide +kernel
theorem fusedMap1328swap_checked : acceptsGraphIso
    (fused (graph core1328) (root 9) 2 0) DegreeTwoThreeSpectrum2100.graph fusedMap1328swap=true := by decide +kernel
theorem certified1328swap : Certified (graph core1328) (root 9) 2 0 :=
  of_native_maps core1328 DegreeTwoThreeSpectrum2099.graph DegreeTwoThreeSpectrum2100.graph
    sourceMap1328swap fusedMap1328swap sourceMap1328swap_checked fusedMap1328swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1328
#print axioms sourceMap1328swap_checked
#print axioms fusedMap1328swap_checked
#print axioms certified1328swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
