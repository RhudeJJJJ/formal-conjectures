/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3969 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap3969 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3969 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3969_checked : acceptsGraphIso
    (source (graph core3969) (root 7) 1 5) DegreeTwoThreeSpectrum4195.graph sourceMap3969=true := by decide +kernel
theorem fusedMap3969_checked : acceptsGraphIso
    (fused (graph core3969) (root 7) 1 5) DegreeTwoThreeSpectrum3894.graph fusedMap3969=true := by decide +kernel
theorem certified3969 : Certified (graph core3969) (root 7) 1 5 :=
  of_native_maps core3969 DegreeTwoThreeSpectrum4195.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap3969 fusedMap3969 sourceMap3969_checked fusedMap3969_checked
    DegreeTwoThreeFiniteComparisons.comparison3969
#print axioms sourceMap3969_checked
#print axioms fusedMap3969_checked
#print axioms certified3969
def sourceMap3969swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3969swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3969swap_checked : acceptsGraphIso
    (source (graph core3969) (root 7) 5 1) DegreeTwoThreeSpectrum4195.graph sourceMap3969swap=true := by decide +kernel
theorem fusedMap3969swap_checked : acceptsGraphIso
    (fused (graph core3969) (root 7) 5 1) DegreeTwoThreeSpectrum3894.graph fusedMap3969swap=true := by decide +kernel
theorem certified3969swap : Certified (graph core3969) (root 7) 5 1 :=
  of_native_maps core3969 DegreeTwoThreeSpectrum4195.graph DegreeTwoThreeSpectrum3894.graph
    sourceMap3969swap fusedMap3969swap sourceMap3969swap_checked fusedMap3969swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3969
#print axioms sourceMap3969swap_checked
#print axioms fusedMap3969swap_checked
#print axioms certified3969swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
