/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5123 : Family 8 := level8.get ⟨28,by decide⟩
def sourceMap5123 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5123 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5123_checked : acceptsGraphIso
    (source (graph core5123) (root 8) 2 4) DegreeTwoThreeSpectrum5902.graph sourceMap5123=true := by decide +kernel
theorem fusedMap5123_checked : acceptsGraphIso
    (fused (graph core5123) (root 8) 2 4) DegreeTwoThreeSpectrum5100.graph fusedMap5123=true := by decide +kernel
theorem certified5123 : Certified (graph core5123) (root 8) 2 4 :=
  of_native_maps core5123 DegreeTwoThreeSpectrum5902.graph DegreeTwoThreeSpectrum5100.graph
    sourceMap5123 fusedMap5123 sourceMap5123_checked fusedMap5123_checked
    DegreeTwoThreeFiniteComparisons.comparison5123
#print axioms sourceMap5123_checked
#print axioms fusedMap5123_checked
#print axioms certified5123
def sourceMap5123swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5123swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5123swap_checked : acceptsGraphIso
    (source (graph core5123) (root 8) 4 2) DegreeTwoThreeSpectrum5902.graph sourceMap5123swap=true := by decide +kernel
theorem fusedMap5123swap_checked : acceptsGraphIso
    (fused (graph core5123) (root 8) 4 2) DegreeTwoThreeSpectrum5100.graph fusedMap5123swap=true := by decide +kernel
theorem certified5123swap : Certified (graph core5123) (root 8) 4 2 :=
  of_native_maps core5123 DegreeTwoThreeSpectrum5902.graph DegreeTwoThreeSpectrum5100.graph
    sourceMap5123swap fusedMap5123swap sourceMap5123swap_checked fusedMap5123swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5123
#print axioms sourceMap5123swap_checked
#print axioms fusedMap5123swap_checked
#print axioms certified5123swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
