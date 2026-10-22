/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1219 : Family 9 := level9.get ⟨122,by decide⟩
def sourceMap1219 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1219 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1219_checked : acceptsGraphIso
    (source (graph core1219) (root 9) 0 2) DegreeTwoThreeSpectrum1881.graph sourceMap1219=true := by decide +kernel
theorem fusedMap1219_checked : acceptsGraphIso
    (fused (graph core1219) (root 9) 0 2) DegreeTwoThreeSpectrum1921.graph fusedMap1219=true := by decide +kernel
theorem certified1219 : Certified (graph core1219) (root 9) 0 2 :=
  of_native_maps core1219 DegreeTwoThreeSpectrum1881.graph DegreeTwoThreeSpectrum1921.graph
    sourceMap1219 fusedMap1219 sourceMap1219_checked fusedMap1219_checked
    DegreeTwoThreeFiniteComparisons.comparison1219
#print axioms sourceMap1219_checked
#print axioms fusedMap1219_checked
#print axioms certified1219
def sourceMap1219swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1219swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1219swap_checked : acceptsGraphIso
    (source (graph core1219) (root 9) 2 0) DegreeTwoThreeSpectrum1881.graph sourceMap1219swap=true := by decide +kernel
theorem fusedMap1219swap_checked : acceptsGraphIso
    (fused (graph core1219) (root 9) 2 0) DegreeTwoThreeSpectrum1921.graph fusedMap1219swap=true := by decide +kernel
theorem certified1219swap : Certified (graph core1219) (root 9) 2 0 :=
  of_native_maps core1219 DegreeTwoThreeSpectrum1881.graph DegreeTwoThreeSpectrum1921.graph
    sourceMap1219swap fusedMap1219swap sourceMap1219swap_checked fusedMap1219swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1219
#print axioms sourceMap1219swap_checked
#print axioms fusedMap1219swap_checked
#print axioms certified1219swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
