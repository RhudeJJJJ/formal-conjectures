/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5225 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5225 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,2,3,4,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5225 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5225_checked : acceptsGraphIso
    (source (graph core5225) (root 5) 2 5) DegreeTwoThreeSpectrum2830.graph sourceMap5225=true := by decide +kernel
theorem fusedMap5225_checked : acceptsGraphIso
    (fused (graph core5225) (root 5) 2 5) DegreeTwoThreeSpectrum2321.graph fusedMap5225=true := by decide +kernel
theorem certified5225 : Certified (graph core5225) (root 5) 2 5 :=
  of_native_maps core5225 DegreeTwoThreeSpectrum2830.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap5225 fusedMap5225 sourceMap5225_checked fusedMap5225_checked
    DegreeTwoThreeFiniteComparisons.comparison5225
#print axioms sourceMap5225_checked
#print axioms fusedMap5225_checked
#print axioms certified5225
def sourceMap5225swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,0,10,11,12,13,14,2,3,4] (sourceLabel 5 5 2 v)
def fusedMap5225swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5225swap_checked : acceptsGraphIso
    (source (graph core5225) (root 5) 5 2) DegreeTwoThreeSpectrum2830.graph sourceMap5225swap=true := by decide +kernel
theorem fusedMap5225swap_checked : acceptsGraphIso
    (fused (graph core5225) (root 5) 5 2) DegreeTwoThreeSpectrum2321.graph fusedMap5225swap=true := by decide +kernel
theorem certified5225swap : Certified (graph core5225) (root 5) 5 2 :=
  of_native_maps core5225 DegreeTwoThreeSpectrum2830.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap5225swap fusedMap5225swap sourceMap5225swap_checked fusedMap5225swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5225
#print axioms sourceMap5225swap_checked
#print axioms fusedMap5225swap_checked
#print axioms certified5225swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
