/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1245 : Family 9 := level9.get ⟨203,by decide⟩
def sourceMap1245 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1245 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1245_checked : acceptsGraphIso
    (source (graph core1245) (root 9) 0 2) DegreeTwoThreeSpectrum2093.graph sourceMap1245=true := by decide +kernel
theorem fusedMap1245_checked : acceptsGraphIso
    (fused (graph core1245) (root 9) 0 2) DegreeTwoThreeSpectrum1806.graph fusedMap1245=true := by decide +kernel
theorem certified1245 : Certified (graph core1245) (root 9) 0 2 :=
  of_native_maps core1245 DegreeTwoThreeSpectrum2093.graph DegreeTwoThreeSpectrum1806.graph
    sourceMap1245 fusedMap1245 sourceMap1245_checked fusedMap1245_checked
    DegreeTwoThreeFiniteComparisons.comparison1245
#print axioms sourceMap1245_checked
#print axioms fusedMap1245_checked
#print axioms certified1245
def sourceMap1245swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1245swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1245swap_checked : acceptsGraphIso
    (source (graph core1245) (root 9) 2 0) DegreeTwoThreeSpectrum2093.graph sourceMap1245swap=true := by decide +kernel
theorem fusedMap1245swap_checked : acceptsGraphIso
    (fused (graph core1245) (root 9) 2 0) DegreeTwoThreeSpectrum1806.graph fusedMap1245swap=true := by decide +kernel
theorem certified1245swap : Certified (graph core1245) (root 9) 2 0 :=
  of_native_maps core1245 DegreeTwoThreeSpectrum2093.graph DegreeTwoThreeSpectrum1806.graph
    sourceMap1245swap fusedMap1245swap sourceMap1245swap_checked fusedMap1245swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1245
#print axioms sourceMap1245swap_checked
#print axioms fusedMap1245swap_checked
#print axioms certified1245swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
