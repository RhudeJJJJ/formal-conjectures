/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5140 : Family 8 := level8.get ⟨86,by decide⟩
def sourceMap5140 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5140 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5140_checked : acceptsGraphIso
    (source (graph core5140) (root 8) 2 4) DegreeTwoThreeSpectrum7030.graph sourceMap5140=true := by decide +kernel
theorem fusedMap5140_checked : acceptsGraphIso
    (fused (graph core5140) (root 8) 2 4) DegreeTwoThreeSpectrum5084.graph fusedMap5140=true := by decide +kernel
theorem certified5140 : Certified (graph core5140) (root 8) 2 4 :=
  of_native_maps core5140 DegreeTwoThreeSpectrum7030.graph DegreeTwoThreeSpectrum5084.graph
    sourceMap5140 fusedMap5140 sourceMap5140_checked fusedMap5140_checked
    DegreeTwoThreeFiniteComparisons.comparison5140
#print axioms sourceMap5140_checked
#print axioms fusedMap5140_checked
#print axioms certified5140
def sourceMap5140swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5140swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5140swap_checked : acceptsGraphIso
    (source (graph core5140) (root 8) 4 2) DegreeTwoThreeSpectrum7030.graph sourceMap5140swap=true := by decide +kernel
theorem fusedMap5140swap_checked : acceptsGraphIso
    (fused (graph core5140) (root 8) 4 2) DegreeTwoThreeSpectrum5084.graph fusedMap5140swap=true := by decide +kernel
theorem certified5140swap : Certified (graph core5140) (root 8) 4 2 :=
  of_native_maps core5140 DegreeTwoThreeSpectrum7030.graph DegreeTwoThreeSpectrum5084.graph
    sourceMap5140swap fusedMap5140swap sourceMap5140swap_checked fusedMap5140swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5140
#print axioms sourceMap5140swap_checked
#print axioms fusedMap5140swap_checked
#print axioms certified5140swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
