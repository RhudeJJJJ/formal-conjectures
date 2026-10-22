/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2286 : Family 9 := level9.get ⟨257,by decide⟩
def sourceMap2286 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2286 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2286_checked : acceptsGraphIso
    (source (graph core2286) (root 9) 0 4) DegreeTwoThreeSpectrum4576.graph sourceMap2286=true := by decide +kernel
theorem fusedMap2286_checked : acceptsGraphIso
    (fused (graph core2286) (root 9) 0 4) DegreeTwoThreeSpectrum4066.graph fusedMap2286=true := by decide +kernel
theorem certified2286 : Certified (graph core2286) (root 9) 0 4 :=
  of_native_maps core2286 DegreeTwoThreeSpectrum4576.graph DegreeTwoThreeSpectrum4066.graph
    sourceMap2286 fusedMap2286 sourceMap2286_checked fusedMap2286_checked
    DegreeTwoThreeFiniteComparisons.comparison2286
#print axioms sourceMap2286_checked
#print axioms fusedMap2286_checked
#print axioms certified2286
def sourceMap2286swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2286swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2286swap_checked : acceptsGraphIso
    (source (graph core2286) (root 9) 4 0) DegreeTwoThreeSpectrum4576.graph sourceMap2286swap=true := by decide +kernel
theorem fusedMap2286swap_checked : acceptsGraphIso
    (fused (graph core2286) (root 9) 4 0) DegreeTwoThreeSpectrum4066.graph fusedMap2286swap=true := by decide +kernel
theorem certified2286swap : Certified (graph core2286) (root 9) 4 0 :=
  of_native_maps core2286 DegreeTwoThreeSpectrum4576.graph DegreeTwoThreeSpectrum4066.graph
    sourceMap2286swap fusedMap2286swap sourceMap2286swap_checked fusedMap2286swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2286
#print axioms sourceMap2286swap_checked
#print axioms fusedMap2286swap_checked
#print axioms certified2286swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
