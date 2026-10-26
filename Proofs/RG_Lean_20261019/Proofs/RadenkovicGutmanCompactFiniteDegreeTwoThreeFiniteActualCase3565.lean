/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3565 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap3565 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3565 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3565_checked : acceptsGraphIso
    (source (graph core3565) (root 8) 0 6) DegreeTwoThreeSpectrum5151.graph sourceMap3565=true := by decide +kernel
theorem fusedMap3565_checked : acceptsGraphIso
    (fused (graph core3565) (root 8) 0 6) DegreeTwoThreeSpectrum5153.graph fusedMap3565=true := by decide +kernel
theorem certified3565 : Certified (graph core3565) (root 8) 0 6 :=
  of_native_maps core3565 DegreeTwoThreeSpectrum5151.graph DegreeTwoThreeSpectrum5153.graph
    sourceMap3565 fusedMap3565 sourceMap3565_checked fusedMap3565_checked
    DegreeTwoThreeFiniteComparisons.comparison3565
#print axioms sourceMap3565_checked
#print axioms fusedMap3565_checked
#print axioms certified3565
def sourceMap3565swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3565swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3565swap_checked : acceptsGraphIso
    (source (graph core3565) (root 8) 6 0) DegreeTwoThreeSpectrum5151.graph sourceMap3565swap=true := by decide +kernel
theorem fusedMap3565swap_checked : acceptsGraphIso
    (fused (graph core3565) (root 8) 6 0) DegreeTwoThreeSpectrum5153.graph fusedMap3565swap=true := by decide +kernel
theorem certified3565swap : Certified (graph core3565) (root 8) 6 0 :=
  of_native_maps core3565 DegreeTwoThreeSpectrum5151.graph DegreeTwoThreeSpectrum5153.graph
    sourceMap3565swap fusedMap3565swap sourceMap3565swap_checked fusedMap3565swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3565
#print axioms sourceMap3565swap_checked
#print axioms fusedMap3565swap_checked
#print axioms certified3565swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
