/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3343 : Family 9 := level9.get ⟨351,by decide⟩
def sourceMap3343 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3343 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3343_checked : acceptsGraphIso
    (source (graph core3343) (root 9) 0 5) DegreeTwoThreeSpectrum6162.graph sourceMap3343=true := by decide +kernel
theorem fusedMap3343_checked : acceptsGraphIso
    (fused (graph core3343) (root 9) 0 5) DegreeTwoThreeSpectrum5202.graph fusedMap3343=true := by decide +kernel
theorem certified3343 : Certified (graph core3343) (root 9) 0 5 :=
  of_native_maps core3343 DegreeTwoThreeSpectrum6162.graph DegreeTwoThreeSpectrum5202.graph
    sourceMap3343 fusedMap3343 sourceMap3343_checked fusedMap3343_checked
    DegreeTwoThreeFiniteComparisons.comparison3343
#print axioms sourceMap3343_checked
#print axioms fusedMap3343_checked
#print axioms certified3343
def sourceMap3343swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3343swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3343swap_checked : acceptsGraphIso
    (source (graph core3343) (root 9) 5 0) DegreeTwoThreeSpectrum6162.graph sourceMap3343swap=true := by decide +kernel
theorem fusedMap3343swap_checked : acceptsGraphIso
    (fused (graph core3343) (root 9) 5 0) DegreeTwoThreeSpectrum5202.graph fusedMap3343swap=true := by decide +kernel
theorem certified3343swap : Certified (graph core3343) (root 9) 5 0 :=
  of_native_maps core3343 DegreeTwoThreeSpectrum6162.graph DegreeTwoThreeSpectrum5202.graph
    sourceMap3343swap fusedMap3343swap sourceMap3343swap_checked fusedMap3343swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3343
#print axioms sourceMap3343swap_checked
#print axioms fusedMap3343swap_checked
#print axioms certified3343swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
