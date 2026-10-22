/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2754 : Family 10 := level10.get ⟨959,by decide⟩
def sourceMap2754 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2754 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2754_checked : acceptsGraphIso
    (source (graph core2754) (root 10) 0 4) DegreeTwoThreeSpectrum7032.graph sourceMap2754=true := by decide +kernel
theorem fusedMap2754_checked : acceptsGraphIso
    (fused (graph core2754) (root 10) 0 4) DegreeTwoThreeSpectrum5868.graph fusedMap2754=true := by decide +kernel
theorem certified2754 : Certified (graph core2754) (root 10) 0 4 :=
  of_native_maps core2754 DegreeTwoThreeSpectrum7032.graph DegreeTwoThreeSpectrum5868.graph
    sourceMap2754 fusedMap2754 sourceMap2754_checked fusedMap2754_checked
    DegreeTwoThreeFiniteComparisons.comparison2754
#print axioms sourceMap2754_checked
#print axioms fusedMap2754_checked
#print axioms certified2754
def sourceMap2754swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2754swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2754swap_checked : acceptsGraphIso
    (source (graph core2754) (root 10) 4 0) DegreeTwoThreeSpectrum7032.graph sourceMap2754swap=true := by decide +kernel
theorem fusedMap2754swap_checked : acceptsGraphIso
    (fused (graph core2754) (root 10) 4 0) DegreeTwoThreeSpectrum5868.graph fusedMap2754swap=true := by decide +kernel
theorem certified2754swap : Certified (graph core2754) (root 10) 4 0 :=
  of_native_maps core2754 DegreeTwoThreeSpectrum7032.graph DegreeTwoThreeSpectrum5868.graph
    sourceMap2754swap fusedMap2754swap sourceMap2754swap_checked fusedMap2754swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2754
#print axioms sourceMap2754swap_checked
#print axioms fusedMap2754swap_checked
#print axioms certified2754swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
