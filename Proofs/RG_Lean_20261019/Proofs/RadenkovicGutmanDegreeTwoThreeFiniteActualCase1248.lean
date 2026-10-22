/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1248 : Family 9 := level9.get ⟨211,by decide⟩
def sourceMap1248 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1248 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1248_checked : acceptsGraphIso
    (source (graph core1248) (root 9) 0 2) DegreeTwoThreeSpectrum2108.graph sourceMap1248=true := by decide +kernel
theorem fusedMap1248_checked : acceptsGraphIso
    (fused (graph core1248) (root 9) 0 2) DegreeTwoThreeSpectrum1816.graph fusedMap1248=true := by decide +kernel
theorem certified1248 : Certified (graph core1248) (root 9) 0 2 :=
  of_native_maps core1248 DegreeTwoThreeSpectrum2108.graph DegreeTwoThreeSpectrum1816.graph
    sourceMap1248 fusedMap1248 sourceMap1248_checked fusedMap1248_checked
    DegreeTwoThreeFiniteComparisons.comparison1248
#print axioms sourceMap1248_checked
#print axioms fusedMap1248_checked
#print axioms certified1248
def sourceMap1248swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1248swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1248swap_checked : acceptsGraphIso
    (source (graph core1248) (root 9) 2 0) DegreeTwoThreeSpectrum2108.graph sourceMap1248swap=true := by decide +kernel
theorem fusedMap1248swap_checked : acceptsGraphIso
    (fused (graph core1248) (root 9) 2 0) DegreeTwoThreeSpectrum1816.graph fusedMap1248swap=true := by decide +kernel
theorem certified1248swap : Certified (graph core1248) (root 9) 2 0 :=
  of_native_maps core1248 DegreeTwoThreeSpectrum2108.graph DegreeTwoThreeSpectrum1816.graph
    sourceMap1248swap fusedMap1248swap sourceMap1248swap_checked fusedMap1248swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1248
#print axioms sourceMap1248swap_checked
#print axioms fusedMap1248swap_checked
#print axioms certified1248swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
