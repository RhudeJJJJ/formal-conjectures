/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2521 : Family 10 := level10.get ⟨280,by decide⟩
def sourceMap2521 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2521 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2521_checked : acceptsGraphIso
    (source (graph core2521) (root 10) 0 4) DegreeTwoThreeSpectrum5414.graph sourceMap2521=true := by decide +kernel
theorem fusedMap2521_checked : acceptsGraphIso
    (fused (graph core2521) (root 10) 0 4) DegreeTwoThreeSpectrum5418.graph fusedMap2521=true := by decide +kernel
theorem certified2521 : Certified (graph core2521) (root 10) 0 4 :=
  of_native_maps core2521 DegreeTwoThreeSpectrum5414.graph DegreeTwoThreeSpectrum5418.graph
    sourceMap2521 fusedMap2521 sourceMap2521_checked fusedMap2521_checked
    DegreeTwoThreeFiniteComparisons.comparison2521
#print axioms sourceMap2521_checked
#print axioms fusedMap2521_checked
#print axioms certified2521
def sourceMap2521swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2521swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2521swap_checked : acceptsGraphIso
    (source (graph core2521) (root 10) 4 0) DegreeTwoThreeSpectrum5414.graph sourceMap2521swap=true := by decide +kernel
theorem fusedMap2521swap_checked : acceptsGraphIso
    (fused (graph core2521) (root 10) 4 0) DegreeTwoThreeSpectrum5418.graph fusedMap2521swap=true := by decide +kernel
theorem certified2521swap : Certified (graph core2521) (root 10) 4 0 :=
  of_native_maps core2521 DegreeTwoThreeSpectrum5414.graph DegreeTwoThreeSpectrum5418.graph
    sourceMap2521swap fusedMap2521swap sourceMap2521swap_checked fusedMap2521swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2521
#print axioms sourceMap2521swap_checked
#print axioms fusedMap2521swap_checked
#print axioms certified2521swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
