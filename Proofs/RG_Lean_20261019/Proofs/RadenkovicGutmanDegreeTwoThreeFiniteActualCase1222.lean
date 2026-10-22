/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1222 : Family 9 := level9.get ⟨130,by decide⟩
def sourceMap1222 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,7,8,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1222 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1222_checked : acceptsGraphIso
    (source (graph core1222) (root 9) 0 2) DegreeTwoThreeSpectrum1879.graph sourceMap1222=true := by decide +kernel
theorem fusedMap1222_checked : acceptsGraphIso
    (fused (graph core1222) (root 9) 0 2) DegreeTwoThreeSpectrum1923.graph fusedMap1222=true := by decide +kernel
theorem certified1222 : Certified (graph core1222) (root 9) 0 2 :=
  of_native_maps core1222 DegreeTwoThreeSpectrum1879.graph DegreeTwoThreeSpectrum1923.graph
    sourceMap1222 fusedMap1222 sourceMap1222_checked fusedMap1222_checked
    DegreeTwoThreeFiniteComparisons.comparison1222
#print axioms sourceMap1222_checked
#print axioms fusedMap1222_checked
#print axioms certified1222
def sourceMap1222swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,7,8,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1222swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1222swap_checked : acceptsGraphIso
    (source (graph core1222) (root 9) 2 0) DegreeTwoThreeSpectrum1879.graph sourceMap1222swap=true := by decide +kernel
theorem fusedMap1222swap_checked : acceptsGraphIso
    (fused (graph core1222) (root 9) 2 0) DegreeTwoThreeSpectrum1923.graph fusedMap1222swap=true := by decide +kernel
theorem certified1222swap : Certified (graph core1222) (root 9) 2 0 :=
  of_native_maps core1222 DegreeTwoThreeSpectrum1879.graph DegreeTwoThreeSpectrum1923.graph
    sourceMap1222swap fusedMap1222swap sourceMap1222swap_checked fusedMap1222swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1222
#print axioms sourceMap1222swap_checked
#print axioms fusedMap1222swap_checked
#print axioms certified1222swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
