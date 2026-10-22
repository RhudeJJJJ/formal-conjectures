/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1281 : Family 9 := level9.get ⟨304,by decide⟩
def sourceMap1281 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1281 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,5,6,7,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1281_checked : acceptsGraphIso
    (source (graph core1281) (root 9) 0 2) DegreeTwoThreeSpectrum2186.graph sourceMap1281=true := by decide +kernel
theorem fusedMap1281_checked : acceptsGraphIso
    (fused (graph core1281) (root 9) 0 2) DegreeTwoThreeSpectrum1906.graph fusedMap1281=true := by decide +kernel
theorem certified1281 : Certified (graph core1281) (root 9) 0 2 :=
  of_native_maps core1281 DegreeTwoThreeSpectrum2186.graph DegreeTwoThreeSpectrum1906.graph
    sourceMap1281 fusedMap1281 sourceMap1281_checked fusedMap1281_checked
    DegreeTwoThreeFiniteComparisons.comparison1281
#print axioms sourceMap1281_checked
#print axioms fusedMap1281_checked
#print axioms certified1281
def sourceMap1281swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1281swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,5,6,7,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1281swap_checked : acceptsGraphIso
    (source (graph core1281) (root 9) 2 0) DegreeTwoThreeSpectrum2186.graph sourceMap1281swap=true := by decide +kernel
theorem fusedMap1281swap_checked : acceptsGraphIso
    (fused (graph core1281) (root 9) 2 0) DegreeTwoThreeSpectrum1906.graph fusedMap1281swap=true := by decide +kernel
theorem certified1281swap : Certified (graph core1281) (root 9) 2 0 :=
  of_native_maps core1281 DegreeTwoThreeSpectrum2186.graph DegreeTwoThreeSpectrum1906.graph
    sourceMap1281swap fusedMap1281swap sourceMap1281swap_checked fusedMap1281swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1281
#print axioms sourceMap1281swap_checked
#print axioms fusedMap1281swap_checked
#print axioms certified1281swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
