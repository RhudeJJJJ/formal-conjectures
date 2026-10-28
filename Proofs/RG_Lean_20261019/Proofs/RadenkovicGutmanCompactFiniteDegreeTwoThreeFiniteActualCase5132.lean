/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5132 : Family 8 := level8.get ⟨60,by decide⟩
def sourceMap5132 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5132 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5132_checked : acceptsGraphIso
    (source (graph core5132) (root 8) 2 4) DegreeTwoThreeSpectrum6671.graph sourceMap5132=true := by decide +kernel
theorem fusedMap5132_checked : acceptsGraphIso
    (fused (graph core5132) (root 8) 2 4) DegreeTwoThreeSpectrum5017.graph fusedMap5132=true := by decide +kernel
theorem certified5132 : Certified (graph core5132) (root 8) 2 4 :=
  of_native_maps core5132 DegreeTwoThreeSpectrum6671.graph DegreeTwoThreeSpectrum5017.graph
    sourceMap5132 fusedMap5132 sourceMap5132_checked fusedMap5132_checked
    DegreeTwoThreeFiniteComparisons.comparison5132
#print axioms sourceMap5132_checked
#print axioms fusedMap5132_checked
#print axioms certified5132
def sourceMap5132swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5132swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5132swap_checked : acceptsGraphIso
    (source (graph core5132) (root 8) 4 2) DegreeTwoThreeSpectrum6671.graph sourceMap5132swap=true := by decide +kernel
theorem fusedMap5132swap_checked : acceptsGraphIso
    (fused (graph core5132) (root 8) 4 2) DegreeTwoThreeSpectrum5017.graph fusedMap5132swap=true := by decide +kernel
theorem certified5132swap : Certified (graph core5132) (root 8) 4 2 :=
  of_native_maps core5132 DegreeTwoThreeSpectrum6671.graph DegreeTwoThreeSpectrum5017.graph
    sourceMap5132swap fusedMap5132swap sourceMap5132swap_checked fusedMap5132swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5132
#print axioms sourceMap5132swap_checked
#print axioms fusedMap5132swap_checked
#print axioms certified5132swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
