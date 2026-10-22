/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2305 : Family 9 := level9.get ⟨305,by decide⟩
def sourceMap2305 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2305 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2305_checked : acceptsGraphIso
    (source (graph core2305) (root 9) 0 4) DegreeTwoThreeSpectrum4656.graph sourceMap2305=true := by decide +kernel
theorem fusedMap2305_checked : acceptsGraphIso
    (fused (graph core2305) (root 9) 0 4) DegreeTwoThreeSpectrum4140.graph fusedMap2305=true := by decide +kernel
theorem certified2305 : Certified (graph core2305) (root 9) 0 4 :=
  of_native_maps core2305 DegreeTwoThreeSpectrum4656.graph DegreeTwoThreeSpectrum4140.graph
    sourceMap2305 fusedMap2305 sourceMap2305_checked fusedMap2305_checked
    DegreeTwoThreeFiniteComparisons.comparison2305
#print axioms sourceMap2305_checked
#print axioms fusedMap2305_checked
#print axioms certified2305
def sourceMap2305swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2305swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2305swap_checked : acceptsGraphIso
    (source (graph core2305) (root 9) 4 0) DegreeTwoThreeSpectrum4656.graph sourceMap2305swap=true := by decide +kernel
theorem fusedMap2305swap_checked : acceptsGraphIso
    (fused (graph core2305) (root 9) 4 0) DegreeTwoThreeSpectrum4140.graph fusedMap2305swap=true := by decide +kernel
theorem certified2305swap : Certified (graph core2305) (root 9) 4 0 :=
  of_native_maps core2305 DegreeTwoThreeSpectrum4656.graph DegreeTwoThreeSpectrum4140.graph
    sourceMap2305swap fusedMap2305swap sourceMap2305swap_checked fusedMap2305swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2305
#print axioms sourceMap2305swap_checked
#print axioms fusedMap2305swap_checked
#print axioms certified2305swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
