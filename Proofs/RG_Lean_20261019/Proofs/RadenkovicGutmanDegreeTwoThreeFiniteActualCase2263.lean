/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2263 : Family 9 := level9.get ⟨190,by decide⟩
def sourceMap2263 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2263 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2263_checked : acceptsGraphIso
    (source (graph core2263) (root 9) 0 4) DegreeTwoThreeSpectrum4381.graph sourceMap2263=true := by decide +kernel
theorem fusedMap2263_checked : acceptsGraphIso
    (fused (graph core2263) (root 9) 0 4) DegreeTwoThreeSpectrum3962.graph fusedMap2263=true := by decide +kernel
theorem certified2263 : Certified (graph core2263) (root 9) 0 4 :=
  of_native_maps core2263 DegreeTwoThreeSpectrum4381.graph DegreeTwoThreeSpectrum3962.graph
    sourceMap2263 fusedMap2263 sourceMap2263_checked fusedMap2263_checked
    DegreeTwoThreeFiniteComparisons.comparison2263
#print axioms sourceMap2263_checked
#print axioms fusedMap2263_checked
#print axioms certified2263
def sourceMap2263swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2263swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2263swap_checked : acceptsGraphIso
    (source (graph core2263) (root 9) 4 0) DegreeTwoThreeSpectrum4381.graph sourceMap2263swap=true := by decide +kernel
theorem fusedMap2263swap_checked : acceptsGraphIso
    (fused (graph core2263) (root 9) 4 0) DegreeTwoThreeSpectrum3962.graph fusedMap2263swap=true := by decide +kernel
theorem certified2263swap : Certified (graph core2263) (root 9) 4 0 :=
  of_native_maps core2263 DegreeTwoThreeSpectrum4381.graph DegreeTwoThreeSpectrum3962.graph
    sourceMap2263swap fusedMap2263swap sourceMap2263swap_checked fusedMap2263swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2263
#print axioms sourceMap2263swap_checked
#print axioms fusedMap2263swap_checked
#print axioms certified2263swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
