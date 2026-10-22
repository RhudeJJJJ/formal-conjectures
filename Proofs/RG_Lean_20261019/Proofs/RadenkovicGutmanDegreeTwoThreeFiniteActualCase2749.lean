/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2749 : Family 10 := level10.get ⟨949,by decide⟩
def sourceMap2749 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2749 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2749_checked : acceptsGraphIso
    (source (graph core2749) (root 10) 0 4) DegreeTwoThreeSpectrum7027.graph sourceMap2749=true := by decide +kernel
theorem fusedMap2749_checked : acceptsGraphIso
    (fused (graph core2749) (root 10) 0 4) DegreeTwoThreeSpectrum5850.graph fusedMap2749=true := by decide +kernel
theorem certified2749 : Certified (graph core2749) (root 10) 0 4 :=
  of_native_maps core2749 DegreeTwoThreeSpectrum7027.graph DegreeTwoThreeSpectrum5850.graph
    sourceMap2749 fusedMap2749 sourceMap2749_checked fusedMap2749_checked
    DegreeTwoThreeFiniteComparisons.comparison2749
#print axioms sourceMap2749_checked
#print axioms fusedMap2749_checked
#print axioms certified2749
def sourceMap2749swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2749swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2749swap_checked : acceptsGraphIso
    (source (graph core2749) (root 10) 4 0) DegreeTwoThreeSpectrum7027.graph sourceMap2749swap=true := by decide +kernel
theorem fusedMap2749swap_checked : acceptsGraphIso
    (fused (graph core2749) (root 10) 4 0) DegreeTwoThreeSpectrum5850.graph fusedMap2749swap=true := by decide +kernel
theorem certified2749swap : Certified (graph core2749) (root 10) 4 0 :=
  of_native_maps core2749 DegreeTwoThreeSpectrum7027.graph DegreeTwoThreeSpectrum5850.graph
    sourceMap2749swap fusedMap2749swap sourceMap2749swap_checked fusedMap2749swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2749
#print axioms sourceMap2749swap_checked
#print axioms fusedMap2749swap_checked
#print axioms certified2749swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
