/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3571 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap3571 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3571 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3571_checked : acceptsGraphIso
    (source (graph core3571) (root 8) 0 6) DegreeTwoThreeSpectrum5274.graph sourceMap3571=true := by decide +kernel
theorem fusedMap3571_checked : acceptsGraphIso
    (fused (graph core3571) (root 8) 0 6) DegreeTwoThreeSpectrum5276.graph fusedMap3571=true := by decide +kernel
theorem certified3571 : Certified (graph core3571) (root 8) 0 6 :=
  of_native_maps core3571 DegreeTwoThreeSpectrum5274.graph DegreeTwoThreeSpectrum5276.graph
    sourceMap3571 fusedMap3571 sourceMap3571_checked fusedMap3571_checked
    DegreeTwoThreeFiniteComparisons.comparison3571
#print axioms sourceMap3571_checked
#print axioms fusedMap3571_checked
#print axioms certified3571
def sourceMap3571swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3571swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3571swap_checked : acceptsGraphIso
    (source (graph core3571) (root 8) 6 0) DegreeTwoThreeSpectrum5274.graph sourceMap3571swap=true := by decide +kernel
theorem fusedMap3571swap_checked : acceptsGraphIso
    (fused (graph core3571) (root 8) 6 0) DegreeTwoThreeSpectrum5276.graph fusedMap3571swap=true := by decide +kernel
theorem certified3571swap : Certified (graph core3571) (root 8) 6 0 :=
  of_native_maps core3571 DegreeTwoThreeSpectrum5274.graph DegreeTwoThreeSpectrum5276.graph
    sourceMap3571swap fusedMap3571swap sourceMap3571swap_checked fusedMap3571swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3571
#print axioms sourceMap3571swap_checked
#print axioms fusedMap3571swap_checked
#print axioms certified3571swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
