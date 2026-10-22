/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1215 : Family 9 := level9.get ⟨109,by decide⟩
def sourceMap1215 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1215 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1215_checked : acceptsGraphIso
    (source (graph core1215) (root 9) 0 2) DegreeTwoThreeSpectrum1880.graph sourceMap1215=true := by decide +kernel
theorem fusedMap1215_checked : acceptsGraphIso
    (fused (graph core1215) (root 9) 0 2) DegreeTwoThreeSpectrum1900.graph fusedMap1215=true := by decide +kernel
theorem certified1215 : Certified (graph core1215) (root 9) 0 2 :=
  of_native_maps core1215 DegreeTwoThreeSpectrum1880.graph DegreeTwoThreeSpectrum1900.graph
    sourceMap1215 fusedMap1215 sourceMap1215_checked fusedMap1215_checked
    DegreeTwoThreeFiniteComparisons.comparison1215
#print axioms sourceMap1215_checked
#print axioms fusedMap1215_checked
#print axioms certified1215
def sourceMap1215swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1215swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,13,12,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1215swap_checked : acceptsGraphIso
    (source (graph core1215) (root 9) 2 0) DegreeTwoThreeSpectrum1880.graph sourceMap1215swap=true := by decide +kernel
theorem fusedMap1215swap_checked : acceptsGraphIso
    (fused (graph core1215) (root 9) 2 0) DegreeTwoThreeSpectrum1900.graph fusedMap1215swap=true := by decide +kernel
theorem certified1215swap : Certified (graph core1215) (root 9) 2 0 :=
  of_native_maps core1215 DegreeTwoThreeSpectrum1880.graph DegreeTwoThreeSpectrum1900.graph
    sourceMap1215swap fusedMap1215swap sourceMap1215swap_checked fusedMap1215swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1215
#print axioms sourceMap1215swap_checked
#print axioms fusedMap1215swap_checked
#print axioms certified1215swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
