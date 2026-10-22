/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3106 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap3106 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3106 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3106_checked : acceptsGraphIso
    (source (graph core3106) (root 7) 0 5) DegreeTwoThreeSpectrum2400.graph sourceMap3106=true := by decide +kernel
theorem fusedMap3106_checked : acceptsGraphIso
    (fused (graph core3106) (root 7) 0 5) DegreeTwoThreeSpectrum2402.graph fusedMap3106=true := by decide +kernel
theorem certified3106 : Certified (graph core3106) (root 7) 0 5 :=
  of_native_maps core3106 DegreeTwoThreeSpectrum2400.graph DegreeTwoThreeSpectrum2402.graph
    sourceMap3106 fusedMap3106 sourceMap3106_checked fusedMap3106_checked
    DegreeTwoThreeFiniteComparisons.comparison3106
#print axioms sourceMap3106_checked
#print axioms fusedMap3106_checked
#print axioms certified3106
def sourceMap3106swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,8] (sourceLabel 7 5 0 v)
def fusedMap3106swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3106swap_checked : acceptsGraphIso
    (source (graph core3106) (root 7) 5 0) DegreeTwoThreeSpectrum2400.graph sourceMap3106swap=true := by decide +kernel
theorem fusedMap3106swap_checked : acceptsGraphIso
    (fused (graph core3106) (root 7) 5 0) DegreeTwoThreeSpectrum2402.graph fusedMap3106swap=true := by decide +kernel
theorem certified3106swap : Certified (graph core3106) (root 7) 5 0 :=
  of_native_maps core3106 DegreeTwoThreeSpectrum2400.graph DegreeTwoThreeSpectrum2402.graph
    sourceMap3106swap fusedMap3106swap sourceMap3106swap_checked fusedMap3106swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3106
#print axioms sourceMap3106swap_checked
#print axioms fusedMap3106swap_checked
#print axioms certified3106swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
