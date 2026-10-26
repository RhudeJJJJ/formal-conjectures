/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3914 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap3914 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3914 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3914_checked : acceptsGraphIso
    (source (graph core3914) (root 8) 1 4) DegreeTwoThreeSpectrum4825.graph sourceMap3914=true := by decide +kernel
theorem fusedMap3914_checked : acceptsGraphIso
    (fused (graph core3914) (root 8) 1 4) DegreeTwoThreeSpectrum4458.graph fusedMap3914=true := by decide +kernel
theorem certified3914 : Certified (graph core3914) (root 8) 1 4 :=
  of_native_maps core3914 DegreeTwoThreeSpectrum4825.graph DegreeTwoThreeSpectrum4458.graph
    sourceMap3914 fusedMap3914 sourceMap3914_checked fusedMap3914_checked
    DegreeTwoThreeFiniteComparisons.comparison3914
#print axioms sourceMap3914_checked
#print axioms fusedMap3914_checked
#print axioms certified3914
def sourceMap3914swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3914swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3914swap_checked : acceptsGraphIso
    (source (graph core3914) (root 8) 4 1) DegreeTwoThreeSpectrum4825.graph sourceMap3914swap=true := by decide +kernel
theorem fusedMap3914swap_checked : acceptsGraphIso
    (fused (graph core3914) (root 8) 4 1) DegreeTwoThreeSpectrum4458.graph fusedMap3914swap=true := by decide +kernel
theorem certified3914swap : Certified (graph core3914) (root 8) 4 1 :=
  of_native_maps core3914 DegreeTwoThreeSpectrum4825.graph DegreeTwoThreeSpectrum4458.graph
    sourceMap3914swap fusedMap3914swap sourceMap3914swap_checked fusedMap3914swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3914
#print axioms sourceMap3914swap_checked
#print axioms fusedMap3914swap_checked
#print axioms certified3914swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
