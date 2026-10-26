/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3911 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap3911 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3911 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3911_checked : acceptsGraphIso
    (source (graph core3911) (root 8) 1 4) DegreeTwoThreeSpectrum4805.graph sourceMap3911=true := by decide +kernel
theorem fusedMap3911_checked : acceptsGraphIso
    (fused (graph core3911) (root 8) 1 4) DegreeTwoThreeSpectrum4419.graph fusedMap3911=true := by decide +kernel
theorem certified3911 : Certified (graph core3911) (root 8) 1 4 :=
  of_native_maps core3911 DegreeTwoThreeSpectrum4805.graph DegreeTwoThreeSpectrum4419.graph
    sourceMap3911 fusedMap3911 sourceMap3911_checked fusedMap3911_checked
    DegreeTwoThreeFiniteComparisons.comparison3911
#print axioms sourceMap3911_checked
#print axioms fusedMap3911_checked
#print axioms certified3911
def sourceMap3911swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3911swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3911swap_checked : acceptsGraphIso
    (source (graph core3911) (root 8) 4 1) DegreeTwoThreeSpectrum4805.graph sourceMap3911swap=true := by decide +kernel
theorem fusedMap3911swap_checked : acceptsGraphIso
    (fused (graph core3911) (root 8) 4 1) DegreeTwoThreeSpectrum4419.graph fusedMap3911swap=true := by decide +kernel
theorem certified3911swap : Certified (graph core3911) (root 8) 4 1 :=
  of_native_maps core3911 DegreeTwoThreeSpectrum4805.graph DegreeTwoThreeSpectrum4419.graph
    sourceMap3911swap fusedMap3911swap sourceMap3911swap_checked fusedMap3911swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3911
#print axioms sourceMap3911swap_checked
#print axioms fusedMap3911swap_checked
#print axioms certified3911swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
