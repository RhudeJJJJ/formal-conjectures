/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5366 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5366 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14,15] (sourceLabel 4 3 6 v)
def fusedMap5366 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 3 6 v)
theorem sourceMap5366_checked : acceptsGraphIso
    (source (graph core5366) (root 4) 3 6) DegreeTwoThreeSpectrum4122.graph sourceMap5366=true := by decide +kernel
theorem fusedMap5366_checked : acceptsGraphIso
    (fused (graph core5366) (root 4) 3 6) DegreeTwoThreeSpectrum3855.graph fusedMap5366=true := by decide +kernel
theorem certified5366 : Certified (graph core5366) (root 4) 3 6 :=
  of_native_maps core5366 DegreeTwoThreeSpectrum4122.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5366 fusedMap5366 sourceMap5366_checked fusedMap5366_checked
    DegreeTwoThreeFiniteComparisons.comparison5366
#print axioms sourceMap5366_checked
#print axioms fusedMap5366_checked
#print axioms certified5366
def sourceMap5366swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,15,2,3,4,5] (sourceLabel 4 6 3 v)
def fusedMap5366swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 6 3 v)
theorem sourceMap5366swap_checked : acceptsGraphIso
    (source (graph core5366) (root 4) 6 3) DegreeTwoThreeSpectrum4122.graph sourceMap5366swap=true := by decide +kernel
theorem fusedMap5366swap_checked : acceptsGraphIso
    (fused (graph core5366) (root 4) 6 3) DegreeTwoThreeSpectrum3855.graph fusedMap5366swap=true := by decide +kernel
theorem certified5366swap : Certified (graph core5366) (root 4) 6 3 :=
  of_native_maps core5366 DegreeTwoThreeSpectrum4122.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap5366swap fusedMap5366swap sourceMap5366swap_checked fusedMap5366swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5366
#print axioms sourceMap5366swap_checked
#print axioms fusedMap5366swap_checked
#print axioms certified5366swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
