/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1233 : Family 9 := level9.get ⟨168,by decide⟩
def sourceMap1233 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1233 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1233_checked : acceptsGraphIso
    (source (graph core1233) (root 9) 0 2) DegreeTwoThreeSpectrum2029.graph sourceMap1233=true := by decide +kernel
theorem fusedMap1233_checked : acceptsGraphIso
    (fused (graph core1233) (root 9) 0 2) DegreeTwoThreeSpectrum1767.graph fusedMap1233=true := by decide +kernel
theorem certified1233 : Certified (graph core1233) (root 9) 0 2 :=
  of_native_maps core1233 DegreeTwoThreeSpectrum2029.graph DegreeTwoThreeSpectrum1767.graph
    sourceMap1233 fusedMap1233 sourceMap1233_checked fusedMap1233_checked
    DegreeTwoThreeFiniteComparisons.comparison1233
#print axioms sourceMap1233_checked
#print axioms fusedMap1233_checked
#print axioms certified1233
def sourceMap1233swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1233swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1233swap_checked : acceptsGraphIso
    (source (graph core1233) (root 9) 2 0) DegreeTwoThreeSpectrum2029.graph sourceMap1233swap=true := by decide +kernel
theorem fusedMap1233swap_checked : acceptsGraphIso
    (fused (graph core1233) (root 9) 2 0) DegreeTwoThreeSpectrum1767.graph fusedMap1233swap=true := by decide +kernel
theorem certified1233swap : Certified (graph core1233) (root 9) 2 0 :=
  of_native_maps core1233 DegreeTwoThreeSpectrum2029.graph DegreeTwoThreeSpectrum1767.graph
    sourceMap1233swap fusedMap1233swap sourceMap1233swap_checked fusedMap1233swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1233
#print axioms sourceMap1233swap_checked
#print axioms fusedMap1233swap_checked
#print axioms certified1233swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
