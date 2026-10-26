/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3609 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap3609 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3609 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3609_checked : acceptsGraphIso
    (source (graph core3609) (root 8) 0 6) DegreeTwoThreeSpectrum6183.graph sourceMap3609=true := by decide +kernel
theorem fusedMap3609_checked : acceptsGraphIso
    (fused (graph core3609) (root 8) 0 6) DegreeTwoThreeSpectrum5225.graph fusedMap3609=true := by decide +kernel
theorem certified3609 : Certified (graph core3609) (root 8) 0 6 :=
  of_native_maps core3609 DegreeTwoThreeSpectrum6183.graph DegreeTwoThreeSpectrum5225.graph
    sourceMap3609 fusedMap3609 sourceMap3609_checked fusedMap3609_checked
    DegreeTwoThreeFiniteComparisons.comparison3609
#print axioms sourceMap3609_checked
#print axioms fusedMap3609_checked
#print axioms certified3609
def sourceMap3609swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3609swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3609swap_checked : acceptsGraphIso
    (source (graph core3609) (root 8) 6 0) DegreeTwoThreeSpectrum6183.graph sourceMap3609swap=true := by decide +kernel
theorem fusedMap3609swap_checked : acceptsGraphIso
    (fused (graph core3609) (root 8) 6 0) DegreeTwoThreeSpectrum5225.graph fusedMap3609swap=true := by decide +kernel
theorem certified3609swap : Certified (graph core3609) (root 8) 6 0 :=
  of_native_maps core3609 DegreeTwoThreeSpectrum6183.graph DegreeTwoThreeSpectrum5225.graph
    sourceMap3609swap fusedMap3609swap sourceMap3609swap_checked fusedMap3609swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3609
#print axioms sourceMap3609swap_checked
#print axioms fusedMap3609swap_checked
#print axioms certified3609swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
