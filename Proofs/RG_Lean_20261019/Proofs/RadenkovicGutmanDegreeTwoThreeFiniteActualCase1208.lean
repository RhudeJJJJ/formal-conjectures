/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1208 : Family 9 := level9.get ⟨83,by decide⟩
def sourceMap1208 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1208 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1208_checked : acceptsGraphIso
    (source (graph core1208) (root 9) 0 2) DegreeTwoThreeSpectrum1840.graph sourceMap1208=true := by decide +kernel
theorem fusedMap1208_checked : acceptsGraphIso
    (fused (graph core1208) (root 9) 0 2) DegreeTwoThreeSpectrum1842.graph fusedMap1208=true := by decide +kernel
theorem certified1208 : Certified (graph core1208) (root 9) 0 2 :=
  of_native_maps core1208 DegreeTwoThreeSpectrum1840.graph DegreeTwoThreeSpectrum1842.graph
    sourceMap1208 fusedMap1208 sourceMap1208_checked fusedMap1208_checked
    DegreeTwoThreeFiniteComparisons.comparison1208
#print axioms sourceMap1208_checked
#print axioms fusedMap1208_checked
#print axioms certified1208
def sourceMap1208swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1208swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1208swap_checked : acceptsGraphIso
    (source (graph core1208) (root 9) 2 0) DegreeTwoThreeSpectrum1840.graph sourceMap1208swap=true := by decide +kernel
theorem fusedMap1208swap_checked : acceptsGraphIso
    (fused (graph core1208) (root 9) 2 0) DegreeTwoThreeSpectrum1842.graph fusedMap1208swap=true := by decide +kernel
theorem certified1208swap : Certified (graph core1208) (root 9) 2 0 :=
  of_native_maps core1208 DegreeTwoThreeSpectrum1840.graph DegreeTwoThreeSpectrum1842.graph
    sourceMap1208swap fusedMap1208swap sourceMap1208swap_checked fusedMap1208swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1208
#print axioms sourceMap1208swap_checked
#print axioms fusedMap1208swap_checked
#print axioms certified1208swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
