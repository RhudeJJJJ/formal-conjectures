/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2193 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap2193 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2193 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2193_checked : acceptsGraphIso
    (source (graph core2193) (root 8) 0 4) DegreeTwoThreeSpectrum3221.graph sourceMap2193=true := by decide +kernel
theorem fusedMap2193_checked : acceptsGraphIso
    (fused (graph core2193) (root 8) 0 4) DegreeTwoThreeSpectrum2522.graph fusedMap2193=true := by decide +kernel
theorem certified2193 : Certified (graph core2193) (root 8) 0 4 :=
  of_native_maps core2193 DegreeTwoThreeSpectrum3221.graph DegreeTwoThreeSpectrum2522.graph
    sourceMap2193 fusedMap2193 sourceMap2193_checked fusedMap2193_checked
    DegreeTwoThreeFiniteComparisons.comparison2193
#print axioms sourceMap2193_checked
#print axioms fusedMap2193_checked
#print axioms certified2193
def sourceMap2193swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2193swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2193swap_checked : acceptsGraphIso
    (source (graph core2193) (root 8) 4 0) DegreeTwoThreeSpectrum3221.graph sourceMap2193swap=true := by decide +kernel
theorem fusedMap2193swap_checked : acceptsGraphIso
    (fused (graph core2193) (root 8) 4 0) DegreeTwoThreeSpectrum2522.graph fusedMap2193swap=true := by decide +kernel
theorem certified2193swap : Certified (graph core2193) (root 8) 4 0 :=
  of_native_maps core2193 DegreeTwoThreeSpectrum3221.graph DegreeTwoThreeSpectrum2522.graph
    sourceMap2193swap fusedMap2193swap sourceMap2193swap_checked fusedMap2193swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2193
#print axioms sourceMap2193swap_checked
#print axioms fusedMap2193swap_checked
#print axioms certified2193swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
