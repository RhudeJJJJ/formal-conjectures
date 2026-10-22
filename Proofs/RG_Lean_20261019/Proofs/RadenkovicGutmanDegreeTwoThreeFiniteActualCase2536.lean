/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2536 : Family 10 := level10.get ⟨339,by decide⟩
def sourceMap2536 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2536 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2536_checked : acceptsGraphIso
    (source (graph core2536) (root 10) 0 4) DegreeTwoThreeSpectrum5590.graph sourceMap2536=true := by decide +kernel
theorem fusedMap2536_checked : acceptsGraphIso
    (fused (graph core2536) (root 10) 0 4) DegreeTwoThreeSpectrum5591.graph fusedMap2536=true := by decide +kernel
theorem certified2536 : Certified (graph core2536) (root 10) 0 4 :=
  of_native_maps core2536 DegreeTwoThreeSpectrum5590.graph DegreeTwoThreeSpectrum5591.graph
    sourceMap2536 fusedMap2536 sourceMap2536_checked fusedMap2536_checked
    DegreeTwoThreeFiniteComparisons.comparison2536
#print axioms sourceMap2536_checked
#print axioms fusedMap2536_checked
#print axioms certified2536
def sourceMap2536swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2536swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2536swap_checked : acceptsGraphIso
    (source (graph core2536) (root 10) 4 0) DegreeTwoThreeSpectrum5590.graph sourceMap2536swap=true := by decide +kernel
theorem fusedMap2536swap_checked : acceptsGraphIso
    (fused (graph core2536) (root 10) 4 0) DegreeTwoThreeSpectrum5591.graph fusedMap2536swap=true := by decide +kernel
theorem certified2536swap : Certified (graph core2536) (root 10) 4 0 :=
  of_native_maps core2536 DegreeTwoThreeSpectrum5590.graph DegreeTwoThreeSpectrum5591.graph
    sourceMap2536swap fusedMap2536swap sourceMap2536swap_checked fusedMap2536swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2536
#print axioms sourceMap2536swap_checked
#print axioms fusedMap2536swap_checked
#print axioms certified2536swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
