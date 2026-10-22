/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5077 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap5077 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5077 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5077_checked : acceptsGraphIso
    (source (graph core5077) (root 6) 2 4) DegreeTwoThreeSpectrum3611.graph sourceMap5077=true := by decide +kernel
theorem fusedMap5077_checked : acceptsGraphIso
    (fused (graph core5077) (root 6) 2 4) DegreeTwoThreeSpectrum2381.graph fusedMap5077=true := by decide +kernel
theorem certified5077 : Certified (graph core5077) (root 6) 2 4 :=
  of_native_maps core5077 DegreeTwoThreeSpectrum3611.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap5077 fusedMap5077 sourceMap5077_checked fusedMap5077_checked
    DegreeTwoThreeFiniteComparisons.comparison5077
#print axioms sourceMap5077_checked
#print axioms fusedMap5077_checked
#print axioms certified5077
def sourceMap5077swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,11,12,13,14,8,9,10] (sourceLabel 6 4 2 v)
def fusedMap5077swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5077swap_checked : acceptsGraphIso
    (source (graph core5077) (root 6) 4 2) DegreeTwoThreeSpectrum3611.graph sourceMap5077swap=true := by decide +kernel
theorem fusedMap5077swap_checked : acceptsGraphIso
    (fused (graph core5077) (root 6) 4 2) DegreeTwoThreeSpectrum2381.graph fusedMap5077swap=true := by decide +kernel
theorem certified5077swap : Certified (graph core5077) (root 6) 4 2 :=
  of_native_maps core5077 DegreeTwoThreeSpectrum3611.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap5077swap fusedMap5077swap sourceMap5077swap_checked fusedMap5077swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5077
#print axioms sourceMap5077swap_checked
#print axioms fusedMap5077swap_checked
#print axioms certified5077swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
