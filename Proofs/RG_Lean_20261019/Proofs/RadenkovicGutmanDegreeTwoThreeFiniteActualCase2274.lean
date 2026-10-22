/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2274 : Family 9 := level9.get ⟨223,by decide⟩
def sourceMap2274 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2274 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2274_checked : acceptsGraphIso
    (source (graph core2274) (root 9) 0 4) DegreeTwoThreeSpectrum4478.graph sourceMap2274=true := by decide +kernel
theorem fusedMap2274_checked : acceptsGraphIso
    (fused (graph core2274) (root 9) 0 4) DegreeTwoThreeSpectrum4011.graph fusedMap2274=true := by decide +kernel
theorem certified2274 : Certified (graph core2274) (root 9) 0 4 :=
  of_native_maps core2274 DegreeTwoThreeSpectrum4478.graph DegreeTwoThreeSpectrum4011.graph
    sourceMap2274 fusedMap2274 sourceMap2274_checked fusedMap2274_checked
    DegreeTwoThreeFiniteComparisons.comparison2274
#print axioms sourceMap2274_checked
#print axioms fusedMap2274_checked
#print axioms certified2274
def sourceMap2274swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2274swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2274swap_checked : acceptsGraphIso
    (source (graph core2274) (root 9) 4 0) DegreeTwoThreeSpectrum4478.graph sourceMap2274swap=true := by decide +kernel
theorem fusedMap2274swap_checked : acceptsGraphIso
    (fused (graph core2274) (root 9) 4 0) DegreeTwoThreeSpectrum4011.graph fusedMap2274swap=true := by decide +kernel
theorem certified2274swap : Certified (graph core2274) (root 9) 4 0 :=
  of_native_maps core2274 DegreeTwoThreeSpectrum4478.graph DegreeTwoThreeSpectrum4011.graph
    sourceMap2274swap fusedMap2274swap sourceMap2274swap_checked fusedMap2274swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2274
#print axioms sourceMap2274swap_checked
#print axioms fusedMap2274swap_checked
#print axioms certified2274swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
