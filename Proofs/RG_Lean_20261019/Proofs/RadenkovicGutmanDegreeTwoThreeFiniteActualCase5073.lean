/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5073 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap5073 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,10,6,7,8,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5073 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5073_checked : acceptsGraphIso
    (source (graph core5073) (root 6) 2 4) DegreeTwoThreeSpectrum3288.graph sourceMap5073=true := by decide +kernel
theorem fusedMap5073_checked : acceptsGraphIso
    (fused (graph core5073) (root 6) 2 4) DegreeTwoThreeSpectrum2328.graph fusedMap5073=true := by decide +kernel
theorem certified5073 : Certified (graph core5073) (root 6) 2 4 :=
  of_native_maps core5073 DegreeTwoThreeSpectrum3288.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap5073 fusedMap5073 sourceMap5073_checked fusedMap5073_checked
    DegreeTwoThreeFiniteComparisons.comparison5073
#print axioms sourceMap5073_checked
#print axioms fusedMap5073_checked
#print axioms certified5073
def sourceMap5073swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,10,0,11,12,13,14,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap5073swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5073swap_checked : acceptsGraphIso
    (source (graph core5073) (root 6) 4 2) DegreeTwoThreeSpectrum3288.graph sourceMap5073swap=true := by decide +kernel
theorem fusedMap5073swap_checked : acceptsGraphIso
    (fused (graph core5073) (root 6) 4 2) DegreeTwoThreeSpectrum2328.graph fusedMap5073swap=true := by decide +kernel
theorem certified5073swap : Certified (graph core5073) (root 6) 4 2 :=
  of_native_maps core5073 DegreeTwoThreeSpectrum3288.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap5073swap fusedMap5073swap sourceMap5073swap_checked fusedMap5073swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5073
#print axioms sourceMap5073swap_checked
#print axioms fusedMap5073swap_checked
#print axioms certified5073swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
