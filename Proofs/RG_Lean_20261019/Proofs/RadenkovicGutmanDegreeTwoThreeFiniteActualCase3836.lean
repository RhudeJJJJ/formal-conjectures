/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3836 : Family 8 := level8.get ⟨47,by decide⟩
def sourceMap3836 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3836 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3836_checked : acceptsGraphIso
    (source (graph core3836) (root 8) 1 4) DegreeTwoThreeSpectrum4367.graph sourceMap3836=true := by decide +kernel
theorem fusedMap3836_checked : acceptsGraphIso
    (fused (graph core3836) (root 8) 1 4) DegreeTwoThreeSpectrum3956.graph fusedMap3836=true := by decide +kernel
theorem certified3836 : Certified (graph core3836) (root 8) 1 4 :=
  of_native_maps core3836 DegreeTwoThreeSpectrum4367.graph DegreeTwoThreeSpectrum3956.graph
    sourceMap3836 fusedMap3836 sourceMap3836_checked fusedMap3836_checked
    DegreeTwoThreeFiniteComparisons.comparison3836
#print axioms sourceMap3836_checked
#print axioms fusedMap3836_checked
#print axioms certified3836
def sourceMap3836swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3836swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3836swap_checked : acceptsGraphIso
    (source (graph core3836) (root 8) 4 1) DegreeTwoThreeSpectrum4367.graph sourceMap3836swap=true := by decide +kernel
theorem fusedMap3836swap_checked : acceptsGraphIso
    (fused (graph core3836) (root 8) 4 1) DegreeTwoThreeSpectrum3956.graph fusedMap3836swap=true := by decide +kernel
theorem certified3836swap : Certified (graph core3836) (root 8) 4 1 :=
  of_native_maps core3836 DegreeTwoThreeSpectrum4367.graph DegreeTwoThreeSpectrum3956.graph
    sourceMap3836swap fusedMap3836swap sourceMap3836swap_checked fusedMap3836swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3836
#print axioms sourceMap3836swap_checked
#print axioms fusedMap3836swap_checked
#print axioms certified3836swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
