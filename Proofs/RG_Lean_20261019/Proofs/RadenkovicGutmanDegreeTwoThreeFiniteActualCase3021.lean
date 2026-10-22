/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3021 : Family 10 := level10.get ⟨1619,by decide⟩
def sourceMap3021 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3021 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3021_checked : acceptsGraphIso
    (source (graph core3021) (root 10) 0 4) DegreeTwoThreeSpectrum7176.graph sourceMap3021=true := by decide +kernel
theorem fusedMap3021_checked : acceptsGraphIso
    (fused (graph core3021) (root 10) 0 4) DegreeTwoThreeSpectrum6174.graph fusedMap3021=true := by decide +kernel
theorem certified3021 : Certified (graph core3021) (root 10) 0 4 :=
  of_native_maps core3021 DegreeTwoThreeSpectrum7176.graph DegreeTwoThreeSpectrum6174.graph
    sourceMap3021 fusedMap3021 sourceMap3021_checked fusedMap3021_checked
    DegreeTwoThreeFiniteComparisons.comparison3021
#print axioms sourceMap3021_checked
#print axioms fusedMap3021_checked
#print axioms certified3021
def sourceMap3021swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3021swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3021swap_checked : acceptsGraphIso
    (source (graph core3021) (root 10) 4 0) DegreeTwoThreeSpectrum7176.graph sourceMap3021swap=true := by decide +kernel
theorem fusedMap3021swap_checked : acceptsGraphIso
    (fused (graph core3021) (root 10) 4 0) DegreeTwoThreeSpectrum6174.graph fusedMap3021swap=true := by decide +kernel
theorem certified3021swap : Certified (graph core3021) (root 10) 4 0 :=
  of_native_maps core3021 DegreeTwoThreeSpectrum7176.graph DegreeTwoThreeSpectrum6174.graph
    sourceMap3021swap fusedMap3021swap sourceMap3021swap_checked fusedMap3021swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3021
#print axioms sourceMap3021swap_checked
#print axioms fusedMap3021swap_checked
#print axioms certified3021swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
