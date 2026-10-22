/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5125 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap5125 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,9,10,6,7,8,1,2,3,4,5] (sourceLabel 8 2 4 v)
def fusedMap5125 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5125_checked : acceptsGraphIso
    (source (graph core5125) (root 8) 2 4) DegreeTwoThreeSpectrum5923.graph sourceMap5125=true := by decide +kernel
theorem fusedMap5125_checked : acceptsGraphIso
    (fused (graph core5125) (root 8) 2 4) DegreeTwoThreeSpectrum5128.graph fusedMap5125=true := by decide +kernel
theorem certified5125 : Certified (graph core5125) (root 8) 2 4 :=
  of_native_maps core5125 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap5125 fusedMap5125 sourceMap5125_checked fusedMap5125_checked
    DegreeTwoThreeFiniteComparisons.comparison5125
#print axioms sourceMap5125_checked
#print axioms fusedMap5125_checked
#print axioms certified5125
def sourceMap5125swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,11,12,13,14,15,16,9,10,1,2,3,4,5,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5125swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5125swap_checked : acceptsGraphIso
    (source (graph core5125) (root 8) 4 2) DegreeTwoThreeSpectrum5923.graph sourceMap5125swap=true := by decide +kernel
theorem fusedMap5125swap_checked : acceptsGraphIso
    (fused (graph core5125) (root 8) 4 2) DegreeTwoThreeSpectrum5128.graph fusedMap5125swap=true := by decide +kernel
theorem certified5125swap : Certified (graph core5125) (root 8) 4 2 :=
  of_native_maps core5125 DegreeTwoThreeSpectrum5923.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap5125swap fusedMap5125swap sourceMap5125swap_checked fusedMap5125swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5125
#print axioms sourceMap5125swap_checked
#print axioms fusedMap5125swap_checked
#print axioms certified5125swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
