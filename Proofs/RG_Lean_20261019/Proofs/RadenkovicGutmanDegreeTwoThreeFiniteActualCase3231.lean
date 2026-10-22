/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3231 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap3231 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3231 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3231_checked : acceptsGraphIso
    (source (graph core3231) (root 8) 0 5) DegreeTwoThreeSpectrum4563.graph sourceMap3231=true := by decide +kernel
theorem fusedMap3231_checked : acceptsGraphIso
    (fused (graph core3231) (root 8) 0 5) DegreeTwoThreeSpectrum4564.graph fusedMap3231=true := by decide +kernel
theorem certified3231 : Certified (graph core3231) (root 8) 0 5 :=
  of_native_maps core3231 DegreeTwoThreeSpectrum4563.graph DegreeTwoThreeSpectrum4564.graph
    sourceMap3231 fusedMap3231 sourceMap3231_checked fusedMap3231_checked
    DegreeTwoThreeFiniteComparisons.comparison3231
#print axioms sourceMap3231_checked
#print axioms fusedMap3231_checked
#print axioms certified3231
def sourceMap3231swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3231swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3231swap_checked : acceptsGraphIso
    (source (graph core3231) (root 8) 5 0) DegreeTwoThreeSpectrum4563.graph sourceMap3231swap=true := by decide +kernel
theorem fusedMap3231swap_checked : acceptsGraphIso
    (fused (graph core3231) (root 8) 5 0) DegreeTwoThreeSpectrum4564.graph fusedMap3231swap=true := by decide +kernel
theorem certified3231swap : Certified (graph core3231) (root 8) 5 0 :=
  of_native_maps core3231 DegreeTwoThreeSpectrum4563.graph DegreeTwoThreeSpectrum4564.graph
    sourceMap3231swap fusedMap3231swap sourceMap3231swap_checked fusedMap3231swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3231
#print axioms sourceMap3231swap_checked
#print axioms fusedMap3231swap_checked
#print axioms certified3231swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
