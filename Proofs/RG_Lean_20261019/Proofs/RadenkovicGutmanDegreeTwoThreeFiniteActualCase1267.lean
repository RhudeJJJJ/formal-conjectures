/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1267 : Family 9 := level9.get ⟨269,by decide⟩
def sourceMap1267 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1267 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1267_checked : acceptsGraphIso
    (source (graph core1267) (root 9) 0 2) DegreeTwoThreeSpectrum2220.graph sourceMap1267=true := by decide +kernel
theorem fusedMap1267_checked : acceptsGraphIso
    (fused (graph core1267) (root 9) 0 2) DegreeTwoThreeSpectrum1877.graph fusedMap1267=true := by decide +kernel
theorem certified1267 : Certified (graph core1267) (root 9) 0 2 :=
  of_native_maps core1267 DegreeTwoThreeSpectrum2220.graph DegreeTwoThreeSpectrum1877.graph
    sourceMap1267 fusedMap1267 sourceMap1267_checked fusedMap1267_checked
    DegreeTwoThreeFiniteComparisons.comparison1267
#print axioms sourceMap1267_checked
#print axioms fusedMap1267_checked
#print axioms certified1267
def sourceMap1267swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1267swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1267swap_checked : acceptsGraphIso
    (source (graph core1267) (root 9) 2 0) DegreeTwoThreeSpectrum2220.graph sourceMap1267swap=true := by decide +kernel
theorem fusedMap1267swap_checked : acceptsGraphIso
    (fused (graph core1267) (root 9) 2 0) DegreeTwoThreeSpectrum1877.graph fusedMap1267swap=true := by decide +kernel
theorem certified1267swap : Certified (graph core1267) (root 9) 2 0 :=
  of_native_maps core1267 DegreeTwoThreeSpectrum2220.graph DegreeTwoThreeSpectrum1877.graph
    sourceMap1267swap fusedMap1267swap sourceMap1267swap_checked fusedMap1267swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1267
#print axioms sourceMap1267swap_checked
#print axioms fusedMap1267swap_checked
#print axioms certified1267swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
