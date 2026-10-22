/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1192 : Family 9 := level9.get ⟨8,by decide⟩
def sourceMap1192 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,7,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1192 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,7,3,4,5,6] (fusedLabel 9 0 2 v)
theorem sourceMap1192_checked : acceptsGraphIso
    (source (graph core1192) (root 9) 0 2) DegreeTwoThreeSpectrum1724.graph sourceMap1192=true := by decide +kernel
theorem fusedMap1192_checked : acceptsGraphIso
    (fused (graph core1192) (root 9) 0 2) DegreeTwoThreeSpectrum1734.graph fusedMap1192=true := by decide +kernel
theorem certified1192 : Certified (graph core1192) (root 9) 0 2 :=
  of_native_maps core1192 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap1192 fusedMap1192 sourceMap1192_checked fusedMap1192_checked
    DegreeTwoThreeFiniteComparisons.comparison1192
#print axioms sourceMap1192_checked
#print axioms fusedMap1192_checked
#print axioms certified1192
def sourceMap1192swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,3,4,5,7] (sourceLabel 9 2 0 v)
def fusedMap1192swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,7,3,4,5,6] (fusedLabel 9 2 0 v)
theorem sourceMap1192swap_checked : acceptsGraphIso
    (source (graph core1192) (root 9) 2 0) DegreeTwoThreeSpectrum1724.graph sourceMap1192swap=true := by decide +kernel
theorem fusedMap1192swap_checked : acceptsGraphIso
    (fused (graph core1192) (root 9) 2 0) DegreeTwoThreeSpectrum1734.graph fusedMap1192swap=true := by decide +kernel
theorem certified1192swap : Certified (graph core1192) (root 9) 2 0 :=
  of_native_maps core1192 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap1192swap fusedMap1192swap sourceMap1192swap_checked fusedMap1192swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1192
#print axioms sourceMap1192swap_checked
#print axioms fusedMap1192swap_checked
#print axioms certified1192swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
