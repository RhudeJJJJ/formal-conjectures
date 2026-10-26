/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3585 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap3585 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3585 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3585_checked : acceptsGraphIso
    (source (graph core3585) (root 8) 0 6) DegreeTwoThreeSpectrum5565.graph sourceMap3585=true := by decide +kernel
theorem fusedMap3585_checked : acceptsGraphIso
    (fused (graph core3585) (root 8) 0 6) DegreeTwoThreeSpectrum5567.graph fusedMap3585=true := by decide +kernel
theorem certified3585 : Certified (graph core3585) (root 8) 0 6 :=
  of_native_maps core3585 DegreeTwoThreeSpectrum5565.graph DegreeTwoThreeSpectrum5567.graph
    sourceMap3585 fusedMap3585 sourceMap3585_checked fusedMap3585_checked
    DegreeTwoThreeFiniteComparisons.comparison3585
#print axioms sourceMap3585_checked
#print axioms fusedMap3585_checked
#print axioms certified3585
def sourceMap3585swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3585swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3585swap_checked : acceptsGraphIso
    (source (graph core3585) (root 8) 6 0) DegreeTwoThreeSpectrum5565.graph sourceMap3585swap=true := by decide +kernel
theorem fusedMap3585swap_checked : acceptsGraphIso
    (fused (graph core3585) (root 8) 6 0) DegreeTwoThreeSpectrum5567.graph fusedMap3585swap=true := by decide +kernel
theorem certified3585swap : Certified (graph core3585) (root 8) 6 0 :=
  of_native_maps core3585 DegreeTwoThreeSpectrum5565.graph DegreeTwoThreeSpectrum5567.graph
    sourceMap3585swap fusedMap3585swap sourceMap3585swap_checked fusedMap3585swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3585
#print axioms sourceMap3585swap_checked
#print axioms fusedMap3585swap_checked
#print axioms certified3585swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
