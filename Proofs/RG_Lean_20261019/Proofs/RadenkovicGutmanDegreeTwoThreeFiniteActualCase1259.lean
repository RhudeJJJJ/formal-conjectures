/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1259 : Family 9 := level9.get ⟨245,by decide⟩
def sourceMap1259 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,10,11,12,7,8,9] (sourceLabel 9 0 2 v)
def fusedMap1259 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1259_checked : acceptsGraphIso
    (source (graph core1259) (root 9) 0 2) DegreeTwoThreeSpectrum2171.graph sourceMap1259=true := by decide +kernel
theorem fusedMap1259_checked : acceptsGraphIso
    (fused (graph core1259) (root 9) 0 2) DegreeTwoThreeSpectrum1849.graph fusedMap1259=true := by decide +kernel
theorem certified1259 : Certified (graph core1259) (root 9) 0 2 :=
  of_native_maps core1259 DegreeTwoThreeSpectrum2171.graph DegreeTwoThreeSpectrum1849.graph
    sourceMap1259 fusedMap1259 sourceMap1259_checked fusedMap1259_checked
    DegreeTwoThreeFiniteComparisons.comparison1259
#print axioms sourceMap1259_checked
#print axioms fusedMap1259_checked
#print axioms certified1259
def sourceMap1259swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,10,11,7,8,9,12] (sourceLabel 9 2 0 v)
def fusedMap1259swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1259swap_checked : acceptsGraphIso
    (source (graph core1259) (root 9) 2 0) DegreeTwoThreeSpectrum2171.graph sourceMap1259swap=true := by decide +kernel
theorem fusedMap1259swap_checked : acceptsGraphIso
    (fused (graph core1259) (root 9) 2 0) DegreeTwoThreeSpectrum1849.graph fusedMap1259swap=true := by decide +kernel
theorem certified1259swap : Certified (graph core1259) (root 9) 2 0 :=
  of_native_maps core1259 DegreeTwoThreeSpectrum2171.graph DegreeTwoThreeSpectrum1849.graph
    sourceMap1259swap fusedMap1259swap sourceMap1259swap_checked fusedMap1259swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1259
#print axioms sourceMap1259swap_checked
#print axioms fusedMap1259swap_checked
#print axioms certified1259swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
