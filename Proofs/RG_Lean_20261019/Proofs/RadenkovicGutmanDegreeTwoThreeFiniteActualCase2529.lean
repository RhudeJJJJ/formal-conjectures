/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2529 : Family 10 := level10.get ⟨313,by decide⟩
def sourceMap2529 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2529 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2529_checked : acceptsGraphIso
    (source (graph core2529) (root 10) 0 4) DegreeTwoThreeSpectrum5515.graph sourceMap2529=true := by decide +kernel
theorem fusedMap2529_checked : acceptsGraphIso
    (fused (graph core2529) (root 10) 0 4) DegreeTwoThreeSpectrum5516.graph fusedMap2529=true := by decide +kernel
theorem certified2529 : Certified (graph core2529) (root 10) 0 4 :=
  of_native_maps core2529 DegreeTwoThreeSpectrum5515.graph DegreeTwoThreeSpectrum5516.graph
    sourceMap2529 fusedMap2529 sourceMap2529_checked fusedMap2529_checked
    DegreeTwoThreeFiniteComparisons.comparison2529
#print axioms sourceMap2529_checked
#print axioms fusedMap2529_checked
#print axioms certified2529
def sourceMap2529swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2529swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2529swap_checked : acceptsGraphIso
    (source (graph core2529) (root 10) 4 0) DegreeTwoThreeSpectrum5515.graph sourceMap2529swap=true := by decide +kernel
theorem fusedMap2529swap_checked : acceptsGraphIso
    (fused (graph core2529) (root 10) 4 0) DegreeTwoThreeSpectrum5516.graph fusedMap2529swap=true := by decide +kernel
theorem certified2529swap : Certified (graph core2529) (root 10) 4 0 :=
  of_native_maps core2529 DegreeTwoThreeSpectrum5515.graph DegreeTwoThreeSpectrum5516.graph
    sourceMap2529swap fusedMap2529swap sourceMap2529swap_checked fusedMap2529swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2529
#print axioms sourceMap2529swap_checked
#print axioms fusedMap2529swap_checked
#print axioms certified2529swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
