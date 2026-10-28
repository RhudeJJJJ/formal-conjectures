/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5317 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5317 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,7,8,4,5,6,2,1,0,9,10,11,12,13,14] (sourceLabel 2 2 8 v)
def fusedMap5317 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 2 8 v)
theorem sourceMap5317_checked : acceptsGraphIso
    (source (graph core5317) (root 2) 2 8) DegreeTwoThreeSpectrum2393.graph sourceMap5317=true := by decide +kernel
theorem fusedMap5317_checked : acceptsGraphIso
    (fused (graph core5317) (root 2) 2 8) DegreeTwoThreeSpectrum2309.graph fusedMap5317=true := by decide +kernel
theorem certified5317 : Certified (graph core5317) (root 2) 2 8 :=
  of_native_maps core5317 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5317 fusedMap5317 sourceMap5317_checked fusedMap5317_checked
    DegreeTwoThreeFiniteComparisons.comparison5317
#print axioms sourceMap5317_checked
#print axioms fusedMap5317_checked
#print axioms certified5317
def sourceMap5317swap : (Vertices 2 ⊕ Fin 9 ⊕ Fin 3) → Fin 15 :=
  fun v => ![3,7,8,2,1,0,9,10,11,12,13,14,4,5,6] (sourceLabel 2 8 2 v)
def fusedMap5317swap : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 8 2 v)
theorem sourceMap5317swap_checked : acceptsGraphIso
    (source (graph core5317) (root 2) 8 2) DegreeTwoThreeSpectrum2393.graph sourceMap5317swap=true := by decide +kernel
theorem fusedMap5317swap_checked : acceptsGraphIso
    (fused (graph core5317) (root 2) 8 2) DegreeTwoThreeSpectrum2309.graph fusedMap5317swap=true := by decide +kernel
theorem certified5317swap : Certified (graph core5317) (root 2) 8 2 :=
  of_native_maps core5317 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap5317swap fusedMap5317swap sourceMap5317swap_checked fusedMap5317swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5317
#print axioms sourceMap5317swap_checked
#print axioms fusedMap5317swap_checked
#print axioms certified5317swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
