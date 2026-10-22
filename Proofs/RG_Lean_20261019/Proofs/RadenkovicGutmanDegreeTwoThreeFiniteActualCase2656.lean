/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2656 : Family 10 := level10.get ⟨697,by decide⟩
def sourceMap2656 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2656 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2656_checked : acceptsGraphIso
    (source (graph core2656) (root 10) 0 4) DegreeTwoThreeSpectrum6523.graph sourceMap2656=true := by decide +kernel
theorem fusedMap2656_checked : acceptsGraphIso
    (fused (graph core2656) (root 10) 0 4) DegreeTwoThreeSpectrum5434.graph fusedMap2656=true := by decide +kernel
theorem certified2656 : Certified (graph core2656) (root 10) 0 4 :=
  of_native_maps core2656 DegreeTwoThreeSpectrum6523.graph DegreeTwoThreeSpectrum5434.graph
    sourceMap2656 fusedMap2656 sourceMap2656_checked fusedMap2656_checked
    DegreeTwoThreeFiniteComparisons.comparison2656
#print axioms sourceMap2656_checked
#print axioms fusedMap2656_checked
#print axioms certified2656
def sourceMap2656swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2656swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2656swap_checked : acceptsGraphIso
    (source (graph core2656) (root 10) 4 0) DegreeTwoThreeSpectrum6523.graph sourceMap2656swap=true := by decide +kernel
theorem fusedMap2656swap_checked : acceptsGraphIso
    (fused (graph core2656) (root 10) 4 0) DegreeTwoThreeSpectrum5434.graph fusedMap2656swap=true := by decide +kernel
theorem certified2656swap : Certified (graph core2656) (root 10) 4 0 :=
  of_native_maps core2656 DegreeTwoThreeSpectrum6523.graph DegreeTwoThreeSpectrum5434.graph
    sourceMap2656swap fusedMap2656swap sourceMap2656swap_checked fusedMap2656swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2656
#print axioms sourceMap2656swap_checked
#print axioms fusedMap2656swap_checked
#print axioms certified2656swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
