/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1307 : Family 9 := level9.get ⟨377,by decide⟩
def sourceMap1307 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1307 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1307_checked : acceptsGraphIso
    (source (graph core1307) (root 9) 0 2) DegreeTwoThreeSpectrum2024.graph sourceMap1307=true := by decide +kernel
theorem fusedMap1307_checked : acceptsGraphIso
    (fused (graph core1307) (root 9) 0 2) DegreeTwoThreeSpectrum2025.graph fusedMap1307=true := by decide +kernel
theorem certified1307 : Certified (graph core1307) (root 9) 0 2 :=
  of_native_maps core1307 DegreeTwoThreeSpectrum2024.graph DegreeTwoThreeSpectrum2025.graph
    sourceMap1307 fusedMap1307 sourceMap1307_checked fusedMap1307_checked
    DegreeTwoThreeFiniteComparisons.comparison1307
#print axioms sourceMap1307_checked
#print axioms fusedMap1307_checked
#print axioms certified1307
def sourceMap1307swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1307swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1307swap_checked : acceptsGraphIso
    (source (graph core1307) (root 9) 2 0) DegreeTwoThreeSpectrum2024.graph sourceMap1307swap=true := by decide +kernel
theorem fusedMap1307swap_checked : acceptsGraphIso
    (fused (graph core1307) (root 9) 2 0) DegreeTwoThreeSpectrum2025.graph fusedMap1307swap=true := by decide +kernel
theorem certified1307swap : Certified (graph core1307) (root 9) 2 0 :=
  of_native_maps core1307 DegreeTwoThreeSpectrum2024.graph DegreeTwoThreeSpectrum2025.graph
    sourceMap1307swap fusedMap1307swap sourceMap1307swap_checked fusedMap1307swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1307
#print axioms sourceMap1307swap_checked
#print axioms fusedMap1307swap_checked
#print axioms certified1307swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
