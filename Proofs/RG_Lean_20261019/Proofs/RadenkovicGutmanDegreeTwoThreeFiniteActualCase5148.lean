/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5148 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap5148 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5148 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5148_checked : acceptsGraphIso
    (source (graph core5148) (root 8) 2 4) DegreeTwoThreeSpectrum6158.graph sourceMap5148=true := by decide +kernel
theorem fusedMap5148_checked : acceptsGraphIso
    (fused (graph core5148) (root 8) 2 4) DegreeTwoThreeSpectrum5205.graph fusedMap5148=true := by decide +kernel
theorem certified5148 : Certified (graph core5148) (root 8) 2 4 :=
  of_native_maps core5148 DegreeTwoThreeSpectrum6158.graph DegreeTwoThreeSpectrum5205.graph
    sourceMap5148 fusedMap5148 sourceMap5148_checked fusedMap5148_checked
    DegreeTwoThreeFiniteComparisons.comparison5148
#print axioms sourceMap5148_checked
#print axioms fusedMap5148_checked
#print axioms certified5148
def sourceMap5148swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5148swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5148swap_checked : acceptsGraphIso
    (source (graph core5148) (root 8) 4 2) DegreeTwoThreeSpectrum6158.graph sourceMap5148swap=true := by decide +kernel
theorem fusedMap5148swap_checked : acceptsGraphIso
    (fused (graph core5148) (root 8) 4 2) DegreeTwoThreeSpectrum5205.graph fusedMap5148swap=true := by decide +kernel
theorem certified5148swap : Certified (graph core5148) (root 8) 4 2 :=
  of_native_maps core5148 DegreeTwoThreeSpectrum6158.graph DegreeTwoThreeSpectrum5205.graph
    sourceMap5148swap fusedMap5148swap sourceMap5148swap_checked fusedMap5148swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5148
#print axioms sourceMap5148swap_checked
#print axioms fusedMap5148swap_checked
#print axioms certified5148swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
