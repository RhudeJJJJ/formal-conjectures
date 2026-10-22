/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3197 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap3197 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3197 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3197_checked : acceptsGraphIso
    (source (graph core3197) (root 8) 0 5) DegreeTwoThreeSpectrum4618.graph sourceMap3197=true := by decide +kernel
theorem fusedMap3197_checked : acceptsGraphIso
    (fused (graph core3197) (root 8) 0 5) DegreeTwoThreeSpectrum4093.graph fusedMap3197=true := by decide +kernel
theorem certified3197 : Certified (graph core3197) (root 8) 0 5 :=
  of_native_maps core3197 DegreeTwoThreeSpectrum4618.graph DegreeTwoThreeSpectrum4093.graph
    sourceMap3197 fusedMap3197 sourceMap3197_checked fusedMap3197_checked
    DegreeTwoThreeFiniteComparisons.comparison3197
#print axioms sourceMap3197_checked
#print axioms fusedMap3197_checked
#print axioms certified3197
def sourceMap3197swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3197swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3197swap_checked : acceptsGraphIso
    (source (graph core3197) (root 8) 5 0) DegreeTwoThreeSpectrum4618.graph sourceMap3197swap=true := by decide +kernel
theorem fusedMap3197swap_checked : acceptsGraphIso
    (fused (graph core3197) (root 8) 5 0) DegreeTwoThreeSpectrum4093.graph fusedMap3197swap=true := by decide +kernel
theorem certified3197swap : Certified (graph core3197) (root 8) 5 0 :=
  of_native_maps core3197 DegreeTwoThreeSpectrum4618.graph DegreeTwoThreeSpectrum4093.graph
    sourceMap3197swap fusedMap3197swap sourceMap3197swap_checked fusedMap3197swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3197
#print axioms sourceMap3197swap_checked
#print axioms fusedMap3197swap_checked
#print axioms certified3197swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
