/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5119 : Family 8 := level8.get ⟨7,by decide⟩
def sourceMap5119 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,10,7,8,9,2,3,4,5,6] (sourceLabel 8 2 4 v)
def fusedMap5119 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5119_checked : acceptsGraphIso
    (source (graph core5119) (root 8) 2 4) DegreeTwoThreeSpectrum5925.graph sourceMap5119=true := by decide +kernel
theorem fusedMap5119_checked : acceptsGraphIso
    (fused (graph core5119) (root 8) 2 4) DegreeTwoThreeSpectrum4965.graph fusedMap5119=true := by decide +kernel
theorem certified5119 : Certified (graph core5119) (root 8) 2 4 :=
  of_native_maps core5119 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap5119 fusedMap5119 sourceMap5119_checked fusedMap5119_checked
    DegreeTwoThreeFiniteComparisons.comparison5119
#print axioms sourceMap5119_checked
#print axioms fusedMap5119_checked
#print axioms certified5119
def sourceMap5119swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,10,2,3,4,5,6,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5119swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5119swap_checked : acceptsGraphIso
    (source (graph core5119) (root 8) 4 2) DegreeTwoThreeSpectrum5925.graph sourceMap5119swap=true := by decide +kernel
theorem fusedMap5119swap_checked : acceptsGraphIso
    (fused (graph core5119) (root 8) 4 2) DegreeTwoThreeSpectrum4965.graph fusedMap5119swap=true := by decide +kernel
theorem certified5119swap : Certified (graph core5119) (root 8) 4 2 :=
  of_native_maps core5119 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap5119swap fusedMap5119swap sourceMap5119swap_checked fusedMap5119swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5119
#print axioms sourceMap5119swap_checked
#print axioms fusedMap5119swap_checked
#print axioms certified5119swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
