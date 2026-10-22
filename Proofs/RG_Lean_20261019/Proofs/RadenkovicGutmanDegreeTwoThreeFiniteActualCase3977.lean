/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3977 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap3977 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3977 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3977_checked : acceptsGraphIso
    (source (graph core3977) (root 7) 1 5) DegreeTwoThreeSpectrum4405.graph sourceMap3977=true := by decide +kernel
theorem fusedMap3977_checked : acceptsGraphIso
    (fused (graph core3977) (root 7) 1 5) DegreeTwoThreeSpectrum3983.graph fusedMap3977=true := by decide +kernel
theorem certified3977 : Certified (graph core3977) (root 7) 1 5 :=
  of_native_maps core3977 DegreeTwoThreeSpectrum4405.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap3977 fusedMap3977 sourceMap3977_checked fusedMap3977_checked
    DegreeTwoThreeFiniteComparisons.comparison3977
#print axioms sourceMap3977_checked
#print axioms fusedMap3977_checked
#print axioms certified3977
def sourceMap3977swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3977swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3977swap_checked : acceptsGraphIso
    (source (graph core3977) (root 7) 5 1) DegreeTwoThreeSpectrum4405.graph sourceMap3977swap=true := by decide +kernel
theorem fusedMap3977swap_checked : acceptsGraphIso
    (fused (graph core3977) (root 7) 5 1) DegreeTwoThreeSpectrum3983.graph fusedMap3977swap=true := by decide +kernel
theorem certified3977swap : Certified (graph core3977) (root 7) 5 1 :=
  of_native_maps core3977 DegreeTwoThreeSpectrum4405.graph DegreeTwoThreeSpectrum3983.graph
    sourceMap3977swap fusedMap3977swap sourceMap3977swap_checked fusedMap3977swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3977
#print axioms sourceMap3977swap_checked
#print axioms fusedMap3977swap_checked
#print axioms certified3977swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
