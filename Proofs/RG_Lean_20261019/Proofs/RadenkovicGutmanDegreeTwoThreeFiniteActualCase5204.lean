/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5204 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap5204 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5204 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5204_checked : acceptsGraphIso
    (source (graph core5204) (root 8) 2 4) DegreeTwoThreeSpectrum7381.graph sourceMap5204=true := by decide +kernel
theorem fusedMap5204_checked : acceptsGraphIso
    (fused (graph core5204) (root 8) 2 4) DegreeTwoThreeSpectrum5482.graph fusedMap5204=true := by decide +kernel
theorem certified5204 : Certified (graph core5204) (root 8) 2 4 :=
  of_native_maps core5204 DegreeTwoThreeSpectrum7381.graph DegreeTwoThreeSpectrum5482.graph
    sourceMap5204 fusedMap5204 sourceMap5204_checked fusedMap5204_checked
    DegreeTwoThreeFiniteComparisons.comparison5204
#print axioms sourceMap5204_checked
#print axioms fusedMap5204_checked
#print axioms certified5204
def sourceMap5204swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5204swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5204swap_checked : acceptsGraphIso
    (source (graph core5204) (root 8) 4 2) DegreeTwoThreeSpectrum7381.graph sourceMap5204swap=true := by decide +kernel
theorem fusedMap5204swap_checked : acceptsGraphIso
    (fused (graph core5204) (root 8) 4 2) DegreeTwoThreeSpectrum5482.graph fusedMap5204swap=true := by decide +kernel
theorem certified5204swap : Certified (graph core5204) (root 8) 4 2 :=
  of_native_maps core5204 DegreeTwoThreeSpectrum7381.graph DegreeTwoThreeSpectrum5482.graph
    sourceMap5204swap fusedMap5204swap sourceMap5204swap_checked fusedMap5204swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5204
#print axioms sourceMap5204swap_checked
#print axioms fusedMap5204swap_checked
#print axioms certified5204swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
