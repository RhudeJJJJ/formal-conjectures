/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1754 : Family 10 := level10.get ⟨1017,by decide⟩
def sourceMap1754 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1754 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1754_checked : acceptsGraphIso
    (source (graph core1754) (root 10) 0 2) DegreeTwoThreeSpectrum3036.graph sourceMap1754=true := by decide +kernel
theorem fusedMap1754_checked : acceptsGraphIso
    (fused (graph core1754) (root 10) 0 2) DegreeTwoThreeSpectrum3037.graph fusedMap1754=true := by decide +kernel
theorem certified1754 : Certified (graph core1754) (root 10) 0 2 :=
  of_native_maps core1754 DegreeTwoThreeSpectrum3036.graph DegreeTwoThreeSpectrum3037.graph
    sourceMap1754 fusedMap1754 sourceMap1754_checked fusedMap1754_checked
    DegreeTwoThreeFiniteComparisons.comparison1754
#print axioms sourceMap1754_checked
#print axioms fusedMap1754_checked
#print axioms certified1754
def sourceMap1754swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1754swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1754swap_checked : acceptsGraphIso
    (source (graph core1754) (root 10) 2 0) DegreeTwoThreeSpectrum3036.graph sourceMap1754swap=true := by decide +kernel
theorem fusedMap1754swap_checked : acceptsGraphIso
    (fused (graph core1754) (root 10) 2 0) DegreeTwoThreeSpectrum3037.graph fusedMap1754swap=true := by decide +kernel
theorem certified1754swap : Certified (graph core1754) (root 10) 2 0 :=
  of_native_maps core1754 DegreeTwoThreeSpectrum3036.graph DegreeTwoThreeSpectrum3037.graph
    sourceMap1754swap fusedMap1754swap sourceMap1754swap_checked fusedMap1754swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1754
#print axioms sourceMap1754swap_checked
#print axioms fusedMap1754swap_checked
#print axioms certified1754swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
