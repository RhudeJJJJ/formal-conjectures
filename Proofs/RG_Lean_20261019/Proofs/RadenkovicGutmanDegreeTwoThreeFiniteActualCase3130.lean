/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3130 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap3130 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3130 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3130_checked : acceptsGraphIso
    (source (graph core3130) (root 7) 0 5) DegreeTwoThreeSpectrum2652.graph sourceMap3130=true := by decide +kernel
theorem fusedMap3130_checked : acceptsGraphIso
    (fused (graph core3130) (root 7) 0 5) DegreeTwoThreeSpectrum2654.graph fusedMap3130=true := by decide +kernel
theorem certified3130 : Certified (graph core3130) (root 7) 0 5 :=
  of_native_maps core3130 DegreeTwoThreeSpectrum2652.graph DegreeTwoThreeSpectrum2654.graph
    sourceMap3130 fusedMap3130 sourceMap3130_checked fusedMap3130_checked
    DegreeTwoThreeFiniteComparisons.comparison3130
#print axioms sourceMap3130_checked
#print axioms fusedMap3130_checked
#print axioms certified3130
def sourceMap3130swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3130swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3130swap_checked : acceptsGraphIso
    (source (graph core3130) (root 7) 5 0) DegreeTwoThreeSpectrum2652.graph sourceMap3130swap=true := by decide +kernel
theorem fusedMap3130swap_checked : acceptsGraphIso
    (fused (graph core3130) (root 7) 5 0) DegreeTwoThreeSpectrum2654.graph fusedMap3130swap=true := by decide +kernel
theorem certified3130swap : Certified (graph core3130) (root 7) 5 0 :=
  of_native_maps core3130 DegreeTwoThreeSpectrum2652.graph DegreeTwoThreeSpectrum2654.graph
    sourceMap3130swap fusedMap3130swap sourceMap3130swap_checked fusedMap3130swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3130
#print axioms sourceMap3130swap_checked
#print axioms fusedMap3130swap_checked
#print axioms certified3130swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
