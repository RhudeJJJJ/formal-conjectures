/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2601 : Family 10 := level10.get ⟨538,by decide⟩
def sourceMap2601 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2601 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2601_checked : acceptsGraphIso
    (source (graph core2601) (root 10) 0 4) DegreeTwoThreeSpectrum6137.graph sourceMap2601=true := by decide +kernel
theorem fusedMap2601_checked : acceptsGraphIso
    (fused (graph core2601) (root 10) 0 4) DegreeTwoThreeSpectrum5187.graph fusedMap2601=true := by decide +kernel
theorem certified2601 : Certified (graph core2601) (root 10) 0 4 :=
  of_native_maps core2601 DegreeTwoThreeSpectrum6137.graph DegreeTwoThreeSpectrum5187.graph
    sourceMap2601 fusedMap2601 sourceMap2601_checked fusedMap2601_checked
    DegreeTwoThreeFiniteComparisons.comparison2601
#print axioms sourceMap2601_checked
#print axioms fusedMap2601_checked
#print axioms certified2601
def sourceMap2601swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2601swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2601swap_checked : acceptsGraphIso
    (source (graph core2601) (root 10) 4 0) DegreeTwoThreeSpectrum6137.graph sourceMap2601swap=true := by decide +kernel
theorem fusedMap2601swap_checked : acceptsGraphIso
    (fused (graph core2601) (root 10) 4 0) DegreeTwoThreeSpectrum5187.graph fusedMap2601swap=true := by decide +kernel
theorem certified2601swap : Certified (graph core2601) (root 10) 4 0 :=
  of_native_maps core2601 DegreeTwoThreeSpectrum6137.graph DegreeTwoThreeSpectrum5187.graph
    sourceMap2601swap fusedMap2601swap sourceMap2601swap_checked fusedMap2601swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2601
#print axioms sourceMap2601swap_checked
#print axioms fusedMap2601swap_checked
#print axioms certified2601swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
