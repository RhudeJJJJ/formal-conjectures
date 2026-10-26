/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3829 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap3829 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3829 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3829_checked : acceptsGraphIso
    (source (graph core3829) (root 8) 1 4) DegreeTwoThreeSpectrum4055.graph sourceMap3829=true := by decide +kernel
theorem fusedMap3829_checked : acceptsGraphIso
    (fused (graph core3829) (root 8) 1 4) DegreeTwoThreeSpectrum3867.graph fusedMap3829=true := by decide +kernel
theorem certified3829 : Certified (graph core3829) (root 8) 1 4 :=
  of_native_maps core3829 DegreeTwoThreeSpectrum4055.graph DegreeTwoThreeSpectrum3867.graph
    sourceMap3829 fusedMap3829 sourceMap3829_checked fusedMap3829_checked
    DegreeTwoThreeFiniteComparisons.comparison3829
#print axioms sourceMap3829_checked
#print axioms fusedMap3829_checked
#print axioms certified3829
def sourceMap3829swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3829swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3829swap_checked : acceptsGraphIso
    (source (graph core3829) (root 8) 4 1) DegreeTwoThreeSpectrum4055.graph sourceMap3829swap=true := by decide +kernel
theorem fusedMap3829swap_checked : acceptsGraphIso
    (fused (graph core3829) (root 8) 4 1) DegreeTwoThreeSpectrum3867.graph fusedMap3829swap=true := by decide +kernel
theorem certified3829swap : Certified (graph core3829) (root 8) 4 1 :=
  of_native_maps core3829 DegreeTwoThreeSpectrum4055.graph DegreeTwoThreeSpectrum3867.graph
    sourceMap3829swap fusedMap3829swap sourceMap3829swap_checked fusedMap3829swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3829
#print axioms sourceMap3829swap_checked
#print axioms fusedMap3829swap_checked
#print axioms certified3829swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
