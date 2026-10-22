/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5070 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap5070 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5070 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5070_checked : acceptsGraphIso
    (source (graph core5070) (root 6) 2 4) DegreeTwoThreeSpectrum2954.graph sourceMap5070=true := by decide +kernel
theorem fusedMap5070_checked : acceptsGraphIso
    (fused (graph core5070) (root 6) 2 4) DegreeTwoThreeSpectrum2414.graph fusedMap5070=true := by decide +kernel
theorem certified5070 : Certified (graph core5070) (root 6) 2 4 :=
  of_native_maps core5070 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap5070 fusedMap5070 sourceMap5070_checked fusedMap5070_checked
    DegreeTwoThreeFiniteComparisons.comparison5070
#print axioms sourceMap5070_checked
#print axioms fusedMap5070_checked
#print axioms certified5070
def sourceMap5070swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,8,9,10,11,12,13,14,5,6,7] (sourceLabel 6 4 2 v)
def fusedMap5070swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5070swap_checked : acceptsGraphIso
    (source (graph core5070) (root 6) 4 2) DegreeTwoThreeSpectrum2954.graph sourceMap5070swap=true := by decide +kernel
theorem fusedMap5070swap_checked : acceptsGraphIso
    (fused (graph core5070) (root 6) 4 2) DegreeTwoThreeSpectrum2414.graph fusedMap5070swap=true := by decide +kernel
theorem certified5070swap : Certified (graph core5070) (root 6) 4 2 :=
  of_native_maps core5070 DegreeTwoThreeSpectrum2954.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap5070swap fusedMap5070swap sourceMap5070swap_checked fusedMap5070swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5070
#print axioms sourceMap5070swap_checked
#print axioms fusedMap5070swap_checked
#print axioms certified5070swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
