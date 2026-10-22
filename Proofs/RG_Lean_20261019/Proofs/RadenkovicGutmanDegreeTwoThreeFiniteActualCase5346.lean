/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5346 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap5346 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5346 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5346_checked : acceptsGraphIso
    (source (graph core5346) (root 6) 3 4) DegreeTwoThreeSpectrum4638.graph sourceMap5346=true := by decide +kernel
theorem fusedMap5346_checked : acceptsGraphIso
    (fused (graph core5346) (root 6) 3 4) DegreeTwoThreeSpectrum4023.graph fusedMap5346=true := by decide +kernel
theorem certified5346 : Certified (graph core5346) (root 6) 3 4 :=
  of_native_maps core5346 DegreeTwoThreeSpectrum4638.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap5346 fusedMap5346 sourceMap5346_checked fusedMap5346_checked
    DegreeTwoThreeFiniteComparisons.comparison5346
#print axioms sourceMap5346_checked
#print axioms fusedMap5346_checked
#print axioms certified5346
def sourceMap5346swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5346swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5346swap_checked : acceptsGraphIso
    (source (graph core5346) (root 6) 4 3) DegreeTwoThreeSpectrum4638.graph sourceMap5346swap=true := by decide +kernel
theorem fusedMap5346swap_checked : acceptsGraphIso
    (fused (graph core5346) (root 6) 4 3) DegreeTwoThreeSpectrum4023.graph fusedMap5346swap=true := by decide +kernel
theorem certified5346swap : Certified (graph core5346) (root 6) 4 3 :=
  of_native_maps core5346 DegreeTwoThreeSpectrum4638.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap5346swap fusedMap5346swap sourceMap5346swap_checked fusedMap5346swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5346
#print axioms sourceMap5346swap_checked
#print axioms fusedMap5346swap_checked
#print axioms certified5346swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
