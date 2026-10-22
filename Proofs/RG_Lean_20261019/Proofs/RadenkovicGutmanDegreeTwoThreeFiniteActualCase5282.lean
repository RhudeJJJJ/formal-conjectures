/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5282 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5282 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,6,7,8,9,3,4,5,1,0,10,11,12,13,14] (sourceLabel 4 2 6 v)
def fusedMap5282 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 2 6 v)
theorem sourceMap5282_checked : acceptsGraphIso
    (source (graph core5282) (root 4) 2 6) DegreeTwoThreeSpectrum2834.graph sourceMap5282=true := by decide +kernel
theorem fusedMap5282_checked : acceptsGraphIso
    (fused (graph core5282) (root 4) 2 6) DegreeTwoThreeSpectrum2327.graph fusedMap5282=true := by decide +kernel
theorem certified5282 : Certified (graph core5282) (root 4) 2 6 :=
  of_native_maps core5282 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap5282 fusedMap5282 sourceMap5282_checked fusedMap5282_checked
    DegreeTwoThreeFiniteComparisons.comparison5282
#print axioms sourceMap5282_checked
#print axioms fusedMap5282_checked
#print axioms certified5282
def sourceMap5282swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,6,7,8,9,1,0,10,11,12,13,14,3,4,5] (sourceLabel 4 6 2 v)
def fusedMap5282swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 6 2 v)
theorem sourceMap5282swap_checked : acceptsGraphIso
    (source (graph core5282) (root 4) 6 2) DegreeTwoThreeSpectrum2834.graph sourceMap5282swap=true := by decide +kernel
theorem fusedMap5282swap_checked : acceptsGraphIso
    (fused (graph core5282) (root 4) 6 2) DegreeTwoThreeSpectrum2327.graph fusedMap5282swap=true := by decide +kernel
theorem certified5282swap : Certified (graph core5282) (root 4) 6 2 :=
  of_native_maps core5282 DegreeTwoThreeSpectrum2834.graph DegreeTwoThreeSpectrum2327.graph
    sourceMap5282swap fusedMap5282swap sourceMap5282swap_checked fusedMap5282swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5282
#print axioms sourceMap5282swap_checked
#print axioms fusedMap5282swap_checked
#print axioms certified5282swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
