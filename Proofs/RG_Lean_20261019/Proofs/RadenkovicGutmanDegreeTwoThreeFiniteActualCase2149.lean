/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2149 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap2149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2149 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2149_checked : acceptsGraphIso
    (source (graph core2149) (root 8) 0 4) DegreeTwoThreeSpectrum2514.graph sourceMap2149=true := by decide +kernel
theorem fusedMap2149_checked : acceptsGraphIso
    (fused (graph core2149) (root 8) 0 4) DegreeTwoThreeSpectrum2516.graph fusedMap2149=true := by decide +kernel
theorem certified2149 : Certified (graph core2149) (root 8) 0 4 :=
  of_native_maps core2149 DegreeTwoThreeSpectrum2514.graph DegreeTwoThreeSpectrum2516.graph
    sourceMap2149 fusedMap2149 sourceMap2149_checked fusedMap2149_checked
    DegreeTwoThreeFiniteComparisons.comparison2149
#print axioms sourceMap2149_checked
#print axioms fusedMap2149_checked
#print axioms certified2149
def sourceMap2149swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2149swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2149swap_checked : acceptsGraphIso
    (source (graph core2149) (root 8) 4 0) DegreeTwoThreeSpectrum2514.graph sourceMap2149swap=true := by decide +kernel
theorem fusedMap2149swap_checked : acceptsGraphIso
    (fused (graph core2149) (root 8) 4 0) DegreeTwoThreeSpectrum2516.graph fusedMap2149swap=true := by decide +kernel
theorem certified2149swap : Certified (graph core2149) (root 8) 4 0 :=
  of_native_maps core2149 DegreeTwoThreeSpectrum2514.graph DegreeTwoThreeSpectrum2516.graph
    sourceMap2149swap fusedMap2149swap sourceMap2149swap_checked fusedMap2149swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2149
#print axioms sourceMap2149swap_checked
#print axioms fusedMap2149swap_checked
#print axioms certified2149swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
