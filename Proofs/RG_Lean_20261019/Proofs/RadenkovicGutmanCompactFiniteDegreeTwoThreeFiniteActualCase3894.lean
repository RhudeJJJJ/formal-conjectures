/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3894 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap3894 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3894 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3894_checked : acceptsGraphIso
    (source (graph core3894) (root 8) 1 4) DegreeTwoThreeSpectrum4704.graph sourceMap3894=true := by decide +kernel
theorem fusedMap3894_checked : acceptsGraphIso
    (fused (graph core3894) (root 8) 1 4) DegreeTwoThreeSpectrum4225.graph fusedMap3894=true := by decide +kernel
theorem certified3894 : Certified (graph core3894) (root 8) 1 4 :=
  of_native_maps core3894 DegreeTwoThreeSpectrum4704.graph DegreeTwoThreeSpectrum4225.graph
    sourceMap3894 fusedMap3894 sourceMap3894_checked fusedMap3894_checked
    DegreeTwoThreeFiniteComparisons.comparison3894
#print axioms sourceMap3894_checked
#print axioms fusedMap3894_checked
#print axioms certified3894
def sourceMap3894swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3894swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3894swap_checked : acceptsGraphIso
    (source (graph core3894) (root 8) 4 1) DegreeTwoThreeSpectrum4704.graph sourceMap3894swap=true := by decide +kernel
theorem fusedMap3894swap_checked : acceptsGraphIso
    (fused (graph core3894) (root 8) 4 1) DegreeTwoThreeSpectrum4225.graph fusedMap3894swap=true := by decide +kernel
theorem certified3894swap : Certified (graph core3894) (root 8) 4 1 :=
  of_native_maps core3894 DegreeTwoThreeSpectrum4704.graph DegreeTwoThreeSpectrum4225.graph
    sourceMap3894swap fusedMap3894swap sourceMap3894swap_checked fusedMap3894swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3894
#print axioms sourceMap3894swap_checked
#print axioms fusedMap3894swap_checked
#print axioms certified3894swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
