/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5218 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5218 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12,13] (sourceLabel 4 2 5 v)
def fusedMap5218 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 2 5 v)
theorem sourceMap5218_checked : acceptsGraphIso
    (source (graph core5218) (root 4) 2 5) DegreeTwoThreeSpectrum1863.graph sourceMap5218=true := by decide +kernel
theorem fusedMap5218_checked : acceptsGraphIso
    (fused (graph core5218) (root 4) 2 5) DegreeTwoThreeSpectrum1710.graph fusedMap5218=true := by decide +kernel
theorem certified5218 : Certified (graph core5218) (root 4) 2 5 :=
  of_native_maps core5218 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap5218 fusedMap5218 sourceMap5218_checked fusedMap5218_checked
    DegreeTwoThreeFiniteComparisons.comparison5218
#print axioms sourceMap5218_checked
#print axioms fusedMap5218_checked
#print axioms certified5218
def sourceMap5218swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,13,2,3,4] (sourceLabel 4 5 2 v)
def fusedMap5218swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 5 2 v)
theorem sourceMap5218swap_checked : acceptsGraphIso
    (source (graph core5218) (root 4) 5 2) DegreeTwoThreeSpectrum1863.graph sourceMap5218swap=true := by decide +kernel
theorem fusedMap5218swap_checked : acceptsGraphIso
    (fused (graph core5218) (root 4) 5 2) DegreeTwoThreeSpectrum1710.graph fusedMap5218swap=true := by decide +kernel
theorem certified5218swap : Certified (graph core5218) (root 4) 5 2 :=
  of_native_maps core5218 DegreeTwoThreeSpectrum1863.graph DegreeTwoThreeSpectrum1710.graph
    sourceMap5218swap fusedMap5218swap sourceMap5218swap_checked fusedMap5218swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5218
#print axioms sourceMap5218swap_checked
#print axioms fusedMap5218swap_checked
#print axioms certified5218swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
