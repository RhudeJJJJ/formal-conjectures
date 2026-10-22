/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2735 : Family 10 := level10.get ⟨912,by decide⟩
def sourceMap2735 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2735 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2735_checked : acceptsGraphIso
    (source (graph core2735) (root 10) 0 4) DegreeTwoThreeSpectrum6985.graph sourceMap2735=true := by decide +kernel
theorem fusedMap2735_checked : acceptsGraphIso
    (fused (graph core2735) (root 10) 0 4) DegreeTwoThreeSpectrum5783.graph fusedMap2735=true := by decide +kernel
theorem certified2735 : Certified (graph core2735) (root 10) 0 4 :=
  of_native_maps core2735 DegreeTwoThreeSpectrum6985.graph DegreeTwoThreeSpectrum5783.graph
    sourceMap2735 fusedMap2735 sourceMap2735_checked fusedMap2735_checked
    DegreeTwoThreeFiniteComparisons.comparison2735
#print axioms sourceMap2735_checked
#print axioms fusedMap2735_checked
#print axioms certified2735
def sourceMap2735swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2735swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2735swap_checked : acceptsGraphIso
    (source (graph core2735) (root 10) 4 0) DegreeTwoThreeSpectrum6985.graph sourceMap2735swap=true := by decide +kernel
theorem fusedMap2735swap_checked : acceptsGraphIso
    (fused (graph core2735) (root 10) 4 0) DegreeTwoThreeSpectrum5783.graph fusedMap2735swap=true := by decide +kernel
theorem certified2735swap : Certified (graph core2735) (root 10) 4 0 :=
  of_native_maps core2735 DegreeTwoThreeSpectrum6985.graph DegreeTwoThreeSpectrum5783.graph
    sourceMap2735swap fusedMap2735swap sourceMap2735swap_checked fusedMap2735swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2735
#print axioms sourceMap2735swap_checked
#print axioms fusedMap2735swap_checked
#print axioms certified2735swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
