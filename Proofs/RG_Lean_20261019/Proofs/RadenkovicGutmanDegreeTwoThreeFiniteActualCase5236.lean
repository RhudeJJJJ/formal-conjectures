/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5236 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap5236 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,6,7,8,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5236 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5236_checked : acceptsGraphIso
    (source (graph core5236) (root 6) 2 5) DegreeTwoThreeSpectrum4483.graph sourceMap5236=true := by decide +kernel
theorem fusedMap5236_checked : acceptsGraphIso
    (fused (graph core5236) (root 6) 2 5) DegreeTwoThreeSpectrum4023.graph fusedMap5236=true := by decide +kernel
theorem certified5236 : Certified (graph core5236) (root 6) 2 5 :=
  of_native_maps core5236 DegreeTwoThreeSpectrum4483.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap5236 fusedMap5236 sourceMap5236_checked fusedMap5236_checked
    DegreeTwoThreeFiniteComparisons.comparison5236
#print axioms sourceMap5236_checked
#print axioms fusedMap5236_checked
#print axioms certified5236
def sourceMap5236swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,0,11,12,13,14,15,6,7,8] (sourceLabel 6 5 2 v)
def fusedMap5236swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5236swap_checked : acceptsGraphIso
    (source (graph core5236) (root 6) 5 2) DegreeTwoThreeSpectrum4483.graph sourceMap5236swap=true := by decide +kernel
theorem fusedMap5236swap_checked : acceptsGraphIso
    (fused (graph core5236) (root 6) 5 2) DegreeTwoThreeSpectrum4023.graph fusedMap5236swap=true := by decide +kernel
theorem certified5236swap : Certified (graph core5236) (root 6) 5 2 :=
  of_native_maps core5236 DegreeTwoThreeSpectrum4483.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap5236swap fusedMap5236swap sourceMap5236swap_checked fusedMap5236swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5236
#print axioms sourceMap5236swap_checked
#print axioms fusedMap5236swap_checked
#print axioms certified5236swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
