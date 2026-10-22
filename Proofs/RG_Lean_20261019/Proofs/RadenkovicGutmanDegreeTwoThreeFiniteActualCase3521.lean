/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3521 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap3521 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3521 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3521_checked : acceptsGraphIso
    (source (graph core3521) (root 7) 0 6) DegreeTwoThreeSpectrum4197.graph sourceMap3521=true := by decide +kernel
theorem fusedMap3521_checked : acceptsGraphIso
    (fused (graph core3521) (root 7) 0 6) DegreeTwoThreeSpectrum3894.graph fusedMap3521=true := by decide +kernel
theorem certified3521 : Certified (graph core3521) (root 7) 0 6 :=
  of_native_maps core3521 DegreeTwoThreeSpectrum4197.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap3521 fusedMap3521 sourceMap3521_checked fusedMap3521_checked
    DegreeTwoThreeFiniteComparisons.comparison3521
#print axioms sourceMap3521_checked
#print axioms fusedMap3521_checked
#print axioms certified3521
def sourceMap3521swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3521swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3521swap_checked : acceptsGraphIso
    (source (graph core3521) (root 7) 6 0) DegreeTwoThreeSpectrum4197.graph sourceMap3521swap=true := by decide +kernel
theorem fusedMap3521swap_checked : acceptsGraphIso
    (fused (graph core3521) (root 7) 6 0) DegreeTwoThreeSpectrum3894.graph fusedMap3521swap=true := by decide +kernel
theorem certified3521swap : Certified (graph core3521) (root 7) 6 0 :=
  of_native_maps core3521 DegreeTwoThreeSpectrum4197.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap3521swap fusedMap3521swap sourceMap3521swap_checked fusedMap3521swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3521
#print axioms sourceMap3521swap_checked
#print axioms fusedMap3521swap_checked
#print axioms certified3521swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
