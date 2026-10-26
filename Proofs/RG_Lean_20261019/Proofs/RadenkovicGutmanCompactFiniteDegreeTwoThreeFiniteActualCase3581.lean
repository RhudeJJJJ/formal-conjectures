/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3581 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap3581 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3581 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3581_checked : acceptsGraphIso
    (source (graph core3581) (root 8) 0 6) DegreeTwoThreeSpectrum5491.graph sourceMap3581=true := by decide +kernel
theorem fusedMap3581_checked : acceptsGraphIso
    (fused (graph core3581) (root 8) 0 6) DegreeTwoThreeSpectrum5493.graph fusedMap3581=true := by decide +kernel
theorem certified3581 : Certified (graph core3581) (root 8) 0 6 :=
  of_native_maps core3581 DegreeTwoThreeSpectrum5491.graph DegreeTwoThreeSpectrum5493.graph
    sourceMap3581 fusedMap3581 sourceMap3581_checked fusedMap3581_checked
    DegreeTwoThreeFiniteComparisons.comparison3581
#print axioms sourceMap3581_checked
#print axioms fusedMap3581_checked
#print axioms certified3581
def sourceMap3581swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3581swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3581swap_checked : acceptsGraphIso
    (source (graph core3581) (root 8) 6 0) DegreeTwoThreeSpectrum5491.graph sourceMap3581swap=true := by decide +kernel
theorem fusedMap3581swap_checked : acceptsGraphIso
    (fused (graph core3581) (root 8) 6 0) DegreeTwoThreeSpectrum5493.graph fusedMap3581swap=true := by decide +kernel
theorem certified3581swap : Certified (graph core3581) (root 8) 6 0 :=
  of_native_maps core3581 DegreeTwoThreeSpectrum5491.graph DegreeTwoThreeSpectrum5493.graph
    sourceMap3581swap fusedMap3581swap sourceMap3581swap_checked fusedMap3581swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3581
#print axioms sourceMap3581swap_checked
#print axioms fusedMap3581swap_checked
#print axioms certified3581swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
