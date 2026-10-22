/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1241 : Family 9 := level9.get ⟨192,by decide⟩
def sourceMap1241 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,11,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1241 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1241_checked : acceptsGraphIso
    (source (graph core1241) (root 9) 0 2) DegreeTwoThreeSpectrum2073.graph sourceMap1241=true := by decide +kernel
theorem fusedMap1241_checked : acceptsGraphIso
    (fused (graph core1241) (root 9) 0 2) DegreeTwoThreeSpectrum1791.graph fusedMap1241=true := by decide +kernel
theorem certified1241 : Certified (graph core1241) (root 9) 0 2 :=
  of_native_maps core1241 DegreeTwoThreeSpectrum2073.graph DegreeTwoThreeSpectrum1791.graph
    sourceMap1241 fusedMap1241 sourceMap1241_checked fusedMap1241_checked
    DegreeTwoThreeFiniteComparisons.comparison1241
#print axioms sourceMap1241_checked
#print axioms fusedMap1241_checked
#print axioms certified1241
def sourceMap1241swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,12,13,10,7,8,9,11] (sourceLabel 9 2 0 v)
def fusedMap1241swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1241swap_checked : acceptsGraphIso
    (source (graph core1241) (root 9) 2 0) DegreeTwoThreeSpectrum2073.graph sourceMap1241swap=true := by decide +kernel
theorem fusedMap1241swap_checked : acceptsGraphIso
    (fused (graph core1241) (root 9) 2 0) DegreeTwoThreeSpectrum1791.graph fusedMap1241swap=true := by decide +kernel
theorem certified1241swap : Certified (graph core1241) (root 9) 2 0 :=
  of_native_maps core1241 DegreeTwoThreeSpectrum2073.graph DegreeTwoThreeSpectrum1791.graph
    sourceMap1241swap fusedMap1241swap sourceMap1241swap_checked fusedMap1241swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1241
#print axioms sourceMap1241swap_checked
#print axioms fusedMap1241swap_checked
#print axioms certified1241swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
