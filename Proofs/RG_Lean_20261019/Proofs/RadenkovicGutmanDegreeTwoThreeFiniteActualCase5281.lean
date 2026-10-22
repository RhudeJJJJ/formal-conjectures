/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5281 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5281 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,9,6,7,8,1,0,10,11,12,13,14] (sourceLabel 4 2 6 v)
def fusedMap5281 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 2 6 v)
theorem sourceMap5281_checked : acceptsGraphIso
    (source (graph core5281) (root 4) 2 6) DegreeTwoThreeSpectrum2819.graph sourceMap5281=true := by decide +kernel
theorem fusedMap5281_checked : acceptsGraphIso
    (fused (graph core5281) (root 4) 2 6) DegreeTwoThreeSpectrum2311.graph fusedMap5281=true := by decide +kernel
theorem certified5281 : Certified (graph core5281) (root 4) 2 6 :=
  of_native_maps core5281 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap5281 fusedMap5281 sourceMap5281_checked fusedMap5281_checked
    DegreeTwoThreeFiniteComparisons.comparison5281
#print axioms sourceMap5281_checked
#print axioms fusedMap5281_checked
#print axioms certified5281
def sourceMap5281swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,3,4,5,9,1,0,10,11,12,13,14,6,7,8] (sourceLabel 4 6 2 v)
def fusedMap5281swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 6 2 v)
theorem sourceMap5281swap_checked : acceptsGraphIso
    (source (graph core5281) (root 4) 6 2) DegreeTwoThreeSpectrum2819.graph sourceMap5281swap=true := by decide +kernel
theorem fusedMap5281swap_checked : acceptsGraphIso
    (fused (graph core5281) (root 4) 6 2) DegreeTwoThreeSpectrum2311.graph fusedMap5281swap=true := by decide +kernel
theorem certified5281swap : Certified (graph core5281) (root 4) 6 2 :=
  of_native_maps core5281 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap5281swap fusedMap5281swap sourceMap5281swap_checked fusedMap5281swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5281
#print axioms sourceMap5281swap_checked
#print axioms fusedMap5281swap_checked
#print axioms certified5281swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
