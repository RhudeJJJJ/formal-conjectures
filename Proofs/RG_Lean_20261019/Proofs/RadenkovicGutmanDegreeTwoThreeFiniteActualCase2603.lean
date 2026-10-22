/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2603 : Family 10 := level10.get ⟨544,by decide⟩
def sourceMap2603 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2603 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2603_checked : acceptsGraphIso
    (source (graph core2603) (root 10) 0 4) DegreeTwoThreeSpectrum6149.graph sourceMap2603=true := by decide +kernel
theorem fusedMap2603_checked : acceptsGraphIso
    (fused (graph core2603) (root 10) 0 4) DegreeTwoThreeSpectrum5194.graph fusedMap2603=true := by decide +kernel
theorem certified2603 : Certified (graph core2603) (root 10) 0 4 :=
  of_native_maps core2603 DegreeTwoThreeSpectrum6149.graph DegreeTwoThreeSpectrum5194.graph
    sourceMap2603 fusedMap2603 sourceMap2603_checked fusedMap2603_checked
    DegreeTwoThreeFiniteComparisons.comparison2603
#print axioms sourceMap2603_checked
#print axioms fusedMap2603_checked
#print axioms certified2603
def sourceMap2603swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2603swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2603swap_checked : acceptsGraphIso
    (source (graph core2603) (root 10) 4 0) DegreeTwoThreeSpectrum6149.graph sourceMap2603swap=true := by decide +kernel
theorem fusedMap2603swap_checked : acceptsGraphIso
    (fused (graph core2603) (root 10) 4 0) DegreeTwoThreeSpectrum5194.graph fusedMap2603swap=true := by decide +kernel
theorem certified2603swap : Certified (graph core2603) (root 10) 4 0 :=
  of_native_maps core2603 DegreeTwoThreeSpectrum6149.graph DegreeTwoThreeSpectrum5194.graph
    sourceMap2603swap fusedMap2603swap sourceMap2603swap_checked fusedMap2603swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2603
#print axioms sourceMap2603swap_checked
#print axioms fusedMap2603swap_checked
#print axioms certified2603swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
