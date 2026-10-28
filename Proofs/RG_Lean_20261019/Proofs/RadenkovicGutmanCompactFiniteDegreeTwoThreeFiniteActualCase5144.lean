/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5144 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap5144 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,14,15,16,11,12,13,6,7,8,9,10] (sourceLabel 8 2 4 v)
def fusedMap5144 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5144_checked : acceptsGraphIso
    (source (graph core5144) (root 8) 2 4) DegreeTwoThreeSpectrum7053.graph sourceMap5144=true := by decide +kernel
theorem fusedMap5144_checked : acceptsGraphIso
    (fused (graph core5144) (root 8) 2 4) DegreeTwoThreeSpectrum5107.graph fusedMap5144=true := by decide +kernel
theorem certified5144 : Certified (graph core5144) (root 8) 2 4 :=
  of_native_maps core5144 DegreeTwoThreeSpectrum7053.graph DegreeTwoThreeSpectrum5107.graph
    sourceMap5144 fusedMap5144 sourceMap5144_checked fusedMap5144_checked
    DegreeTwoThreeFiniteComparisons.comparison5144
#print axioms sourceMap5144_checked
#print axioms fusedMap5144_checked
#print axioms certified5144
def sourceMap5144swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,14,15,16,6,7,8,9,10,11,12,13] (sourceLabel 8 4 2 v)
def fusedMap5144swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5144swap_checked : acceptsGraphIso
    (source (graph core5144) (root 8) 4 2) DegreeTwoThreeSpectrum7053.graph sourceMap5144swap=true := by decide +kernel
theorem fusedMap5144swap_checked : acceptsGraphIso
    (fused (graph core5144) (root 8) 4 2) DegreeTwoThreeSpectrum5107.graph fusedMap5144swap=true := by decide +kernel
theorem certified5144swap : Certified (graph core5144) (root 8) 4 2 :=
  of_native_maps core5144 DegreeTwoThreeSpectrum7053.graph DegreeTwoThreeSpectrum5107.graph
    sourceMap5144swap fusedMap5144swap sourceMap5144swap_checked fusedMap5144swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5144
#print axioms sourceMap5144swap_checked
#print axioms fusedMap5144swap_checked
#print axioms certified5144swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
