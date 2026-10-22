/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5079 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap5079 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5079 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5079_checked : acceptsGraphIso
    (source (graph core5079) (root 6) 2 4) DegreeTwoThreeSpectrum3638.graph sourceMap5079=true := by decide +kernel
theorem fusedMap5079_checked : acceptsGraphIso
    (fused (graph core5079) (root 6) 2 4) DegreeTwoThreeSpectrum2444.graph fusedMap5079=true := by decide +kernel
theorem certified5079 : Certified (graph core5079) (root 6) 2 4 :=
  of_native_maps core5079 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap5079 fusedMap5079 sourceMap5079_checked fusedMap5079_checked
    DegreeTwoThreeFiniteComparisons.comparison5079
#print axioms sourceMap5079_checked
#print axioms fusedMap5079_checked
#print axioms certified5079
def sourceMap5079swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,2,3,4] (sourceLabel 6 4 2 v)
def fusedMap5079swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5079swap_checked : acceptsGraphIso
    (source (graph core5079) (root 6) 4 2) DegreeTwoThreeSpectrum3638.graph sourceMap5079swap=true := by decide +kernel
theorem fusedMap5079swap_checked : acceptsGraphIso
    (fused (graph core5079) (root 6) 4 2) DegreeTwoThreeSpectrum2444.graph fusedMap5079swap=true := by decide +kernel
theorem certified5079swap : Certified (graph core5079) (root 6) 4 2 :=
  of_native_maps core5079 DegreeTwoThreeSpectrum3638.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap5079swap fusedMap5079swap sourceMap5079swap_checked fusedMap5079swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5079
#print axioms sourceMap5079swap_checked
#print axioms fusedMap5079swap_checked
#print axioms certified5079swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
