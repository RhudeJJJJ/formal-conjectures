/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5201 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap5201 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5201 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5201_checked : acceptsGraphIso
    (source (graph core5201) (root 8) 2 4) DegreeTwoThreeSpectrum7341.graph sourceMap5201=true := by decide +kernel
theorem fusedMap5201_checked : acceptsGraphIso
    (fused (graph core5201) (root 8) 2 4) DegreeTwoThreeSpectrum5427.graph fusedMap5201=true := by decide +kernel
theorem certified5201 : Certified (graph core5201) (root 8) 2 4 :=
  of_native_maps core5201 DegreeTwoThreeSpectrum7341.graph DegreeTwoThreeSpectrum5427.graph
    sourceMap5201 fusedMap5201 sourceMap5201_checked fusedMap5201_checked
    DegreeTwoThreeFiniteComparisons.comparison5201
#print axioms sourceMap5201_checked
#print axioms fusedMap5201_checked
#print axioms certified5201
def sourceMap5201swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5201swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5201swap_checked : acceptsGraphIso
    (source (graph core5201) (root 8) 4 2) DegreeTwoThreeSpectrum7341.graph sourceMap5201swap=true := by decide +kernel
theorem fusedMap5201swap_checked : acceptsGraphIso
    (fused (graph core5201) (root 8) 4 2) DegreeTwoThreeSpectrum5427.graph fusedMap5201swap=true := by decide +kernel
theorem certified5201swap : Certified (graph core5201) (root 8) 4 2 :=
  of_native_maps core5201 DegreeTwoThreeSpectrum7341.graph DegreeTwoThreeSpectrum5427.graph
    sourceMap5201swap fusedMap5201swap sourceMap5201swap_checked fusedMap5201swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5201
#print axioms sourceMap5201swap_checked
#print axioms fusedMap5201swap_checked
#print axioms certified5201swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
