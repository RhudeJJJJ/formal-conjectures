/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5302 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap5302 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,9,10,11,6,7,8,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5302 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5302_checked : acceptsGraphIso
    (source (graph core5302) (root 6) 2 6) DegreeTwoThreeSpectrum6803.graph sourceMap5302=true := by decide +kernel
theorem fusedMap5302_checked : acceptsGraphIso
    (fused (graph core5302) (root 6) 2 6) DegreeTwoThreeSpectrum5049.graph fusedMap5302=true := by decide +kernel
theorem certified5302 : Certified (graph core5302) (root 6) 2 6 :=
  of_native_maps core5302 DegreeTwoThreeSpectrum6803.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap5302 fusedMap5302 sourceMap5302_checked fusedMap5302_checked
    DegreeTwoThreeFiniteComparisons.comparison5302
#print axioms sourceMap5302_checked
#print axioms fusedMap5302_checked
#print axioms certified5302
def sourceMap5302swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,9,10,11,1,0,12,13,14,15,16,6,7,8] (sourceLabel 6 6 2 v)
def fusedMap5302swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5302swap_checked : acceptsGraphIso
    (source (graph core5302) (root 6) 6 2) DegreeTwoThreeSpectrum6803.graph sourceMap5302swap=true := by decide +kernel
theorem fusedMap5302swap_checked : acceptsGraphIso
    (fused (graph core5302) (root 6) 6 2) DegreeTwoThreeSpectrum5049.graph fusedMap5302swap=true := by decide +kernel
theorem certified5302swap : Certified (graph core5302) (root 6) 6 2 :=
  of_native_maps core5302 DegreeTwoThreeSpectrum6803.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap5302swap fusedMap5302swap sourceMap5302swap_checked fusedMap5302swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5302
#print axioms sourceMap5302swap_checked
#print axioms fusedMap5302swap_checked
#print axioms certified5302swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
