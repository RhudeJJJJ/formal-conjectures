/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1207 : Family 9 := level9.get ⟨78,by decide⟩
def sourceMap1207 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1207 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1207_checked : acceptsGraphIso
    (source (graph core1207) (root 9) 0 2) DegreeTwoThreeSpectrum1827.graph sourceMap1207=true := by decide +kernel
theorem fusedMap1207_checked : acceptsGraphIso
    (fused (graph core1207) (root 9) 0 2) DegreeTwoThreeSpectrum1829.graph fusedMap1207=true := by decide +kernel
theorem certified1207 : Certified (graph core1207) (root 9) 0 2 :=
  of_native_maps core1207 DegreeTwoThreeSpectrum1827.graph DegreeTwoThreeSpectrum1829.graph
    sourceMap1207 fusedMap1207 sourceMap1207_checked fusedMap1207_checked
    DegreeTwoThreeFiniteComparisons.comparison1207
#print axioms sourceMap1207_checked
#print axioms fusedMap1207_checked
#print axioms certified1207
def sourceMap1207swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1207swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1207swap_checked : acceptsGraphIso
    (source (graph core1207) (root 9) 2 0) DegreeTwoThreeSpectrum1827.graph sourceMap1207swap=true := by decide +kernel
theorem fusedMap1207swap_checked : acceptsGraphIso
    (fused (graph core1207) (root 9) 2 0) DegreeTwoThreeSpectrum1829.graph fusedMap1207swap=true := by decide +kernel
theorem certified1207swap : Certified (graph core1207) (root 9) 2 0 :=
  of_native_maps core1207 DegreeTwoThreeSpectrum1827.graph DegreeTwoThreeSpectrum1829.graph
    sourceMap1207swap fusedMap1207swap sourceMap1207swap_checked fusedMap1207swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1207
#print axioms sourceMap1207swap_checked
#print axioms fusedMap1207swap_checked
#print axioms certified1207swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
