/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3555 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap3555 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3555 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3555_checked : acceptsGraphIso
    (source (graph core3555) (root 8) 0 6) DegreeTwoThreeSpectrum5638.graph sourceMap3555=true := by decide +kernel
theorem fusedMap3555_checked : acceptsGraphIso
    (fused (graph core3555) (root 8) 0 6) DegreeTwoThreeSpectrum5034.graph fusedMap3555=true := by decide +kernel
theorem certified3555 : Certified (graph core3555) (root 8) 0 6 :=
  of_native_maps core3555 DegreeTwoThreeSpectrum5638.graph DegreeTwoThreeSpectrum5034.graph
    sourceMap3555 fusedMap3555 sourceMap3555_checked fusedMap3555_checked
    DegreeTwoThreeFiniteComparisons.comparison3555
#print axioms sourceMap3555_checked
#print axioms fusedMap3555_checked
#print axioms certified3555
def sourceMap3555swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3555swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3555swap_checked : acceptsGraphIso
    (source (graph core3555) (root 8) 6 0) DegreeTwoThreeSpectrum5638.graph sourceMap3555swap=true := by decide +kernel
theorem fusedMap3555swap_checked : acceptsGraphIso
    (fused (graph core3555) (root 8) 6 0) DegreeTwoThreeSpectrum5034.graph fusedMap3555swap=true := by decide +kernel
theorem certified3555swap : Certified (graph core3555) (root 8) 6 0 :=
  of_native_maps core3555 DegreeTwoThreeSpectrum5638.graph DegreeTwoThreeSpectrum5034.graph
    sourceMap3555swap fusedMap3555swap sourceMap3555swap_checked fusedMap3555swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3555
#print axioms sourceMap3555swap_checked
#print axioms fusedMap3555swap_checked
#print axioms certified3555swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
