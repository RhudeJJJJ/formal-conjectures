/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2257 : Family 9 := level9.get ⟨171,by decide⟩
def sourceMap2257 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2257 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2257_checked : acceptsGraphIso
    (source (graph core2257) (root 9) 0 4) DegreeTwoThreeSpectrum4326.graph sourceMap2257=true := by decide +kernel
theorem fusedMap2257_checked : acceptsGraphIso
    (fused (graph core2257) (root 9) 0 4) DegreeTwoThreeSpectrum3934.graph fusedMap2257=true := by decide +kernel
theorem certified2257 : Certified (graph core2257) (root 9) 0 4 :=
  of_native_maps core2257 DegreeTwoThreeSpectrum4326.graph DegreeTwoThreeSpectrum3934.graph
    sourceMap2257 fusedMap2257 sourceMap2257_checked fusedMap2257_checked
    DegreeTwoThreeFiniteComparisons.comparison2257
#print axioms sourceMap2257_checked
#print axioms fusedMap2257_checked
#print axioms certified2257
def sourceMap2257swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2257swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2257swap_checked : acceptsGraphIso
    (source (graph core2257) (root 9) 4 0) DegreeTwoThreeSpectrum4326.graph sourceMap2257swap=true := by decide +kernel
theorem fusedMap2257swap_checked : acceptsGraphIso
    (fused (graph core2257) (root 9) 4 0) DegreeTwoThreeSpectrum3934.graph fusedMap2257swap=true := by decide +kernel
theorem certified2257swap : Certified (graph core2257) (root 9) 4 0 :=
  of_native_maps core2257 DegreeTwoThreeSpectrum4326.graph DegreeTwoThreeSpectrum3934.graph
    sourceMap2257swap fusedMap2257swap sourceMap2257swap_checked fusedMap2257swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2257
#print axioms sourceMap2257swap_checked
#print axioms fusedMap2257swap_checked
#print axioms certified2257swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
