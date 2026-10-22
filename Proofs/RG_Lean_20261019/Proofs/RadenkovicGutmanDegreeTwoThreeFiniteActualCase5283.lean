/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5283 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5283 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,6,7,8,9,3,4,5,1,0,10,11,12,13,14] (sourceLabel 4 2 6 v)
def fusedMap5283 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 2 6 v)
theorem sourceMap5283_checked : acceptsGraphIso
    (source (graph core5283) (root 4) 2 6) DegreeTwoThreeSpectrum2842.graph sourceMap5283=true := by decide +kernel
theorem fusedMap5283_checked : acceptsGraphIso
    (fused (graph core5283) (root 4) 2 6) DegreeTwoThreeSpectrum2354.graph fusedMap5283=true := by decide +kernel
theorem certified5283 : Certified (graph core5283) (root 4) 2 6 :=
  of_native_maps core5283 DegreeTwoThreeSpectrum2842.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap5283 fusedMap5283 sourceMap5283_checked fusedMap5283_checked
    DegreeTwoThreeFiniteComparisons.comparison5283
#print axioms sourceMap5283_checked
#print axioms fusedMap5283_checked
#print axioms certified5283
def sourceMap5283swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,6,7,8,9,1,0,10,11,12,13,14,3,4,5] (sourceLabel 4 6 2 v)
def fusedMap5283swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 6 2 v)
theorem sourceMap5283swap_checked : acceptsGraphIso
    (source (graph core5283) (root 4) 6 2) DegreeTwoThreeSpectrum2842.graph sourceMap5283swap=true := by decide +kernel
theorem fusedMap5283swap_checked : acceptsGraphIso
    (fused (graph core5283) (root 4) 6 2) DegreeTwoThreeSpectrum2354.graph fusedMap5283swap=true := by decide +kernel
theorem certified5283swap : Certified (graph core5283) (root 4) 6 2 :=
  of_native_maps core5283 DegreeTwoThreeSpectrum2842.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap5283swap fusedMap5283swap sourceMap5283swap_checked fusedMap5283swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5283
#print axioms sourceMap5283swap_checked
#print axioms fusedMap5283swap_checked
#print axioms certified5283swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
