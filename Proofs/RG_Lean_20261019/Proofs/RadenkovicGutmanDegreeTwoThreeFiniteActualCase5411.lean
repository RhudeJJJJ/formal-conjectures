/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5411 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5411 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,7,8,9,10,2,3,4,5,6,0,11,12,13,14,15,16] (sourceLabel 4 4 6 v)
def fusedMap5411 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 4 6 v)
theorem sourceMap5411_checked : acceptsGraphIso
    (source (graph core5411) (root 4) 4 6) DegreeTwoThreeSpectrum5925.graph sourceMap5411=true := by decide +kernel
theorem fusedMap5411_checked : acceptsGraphIso
    (fused (graph core5411) (root 4) 4 6) DegreeTwoThreeSpectrum4961.graph fusedMap5411=true := by decide +kernel
theorem certified5411 : Certified (graph core5411) (root 4) 4 6 :=
  of_native_maps core5411 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap5411 fusedMap5411 sourceMap5411_checked fusedMap5411_checked
    DegreeTwoThreeFiniteComparisons.comparison5411
#print axioms sourceMap5411_checked
#print axioms fusedMap5411_checked
#print axioms certified5411
def sourceMap5411swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,7,8,9,10,0,11,12,13,14,15,16,2,3,4,5,6] (sourceLabel 4 6 4 v)
def fusedMap5411swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 6 4 v)
theorem sourceMap5411swap_checked : acceptsGraphIso
    (source (graph core5411) (root 4) 6 4) DegreeTwoThreeSpectrum5925.graph sourceMap5411swap=true := by decide +kernel
theorem fusedMap5411swap_checked : acceptsGraphIso
    (fused (graph core5411) (root 4) 6 4) DegreeTwoThreeSpectrum4961.graph fusedMap5411swap=true := by decide +kernel
theorem certified5411swap : Certified (graph core5411) (root 4) 6 4 :=
  of_native_maps core5411 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap5411swap fusedMap5411swap sourceMap5411swap_checked fusedMap5411swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5411
#print axioms sourceMap5411swap_checked
#print axioms fusedMap5411swap_checked
#print axioms certified5411swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
