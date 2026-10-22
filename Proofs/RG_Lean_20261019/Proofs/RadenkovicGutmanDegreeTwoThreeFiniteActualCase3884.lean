/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3884 : Family 8 := level8.get ⟨176,by decide⟩
def sourceMap3884 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3884 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3884_checked : acceptsGraphIso
    (source (graph core3884) (root 8) 1 4) DegreeTwoThreeSpectrum4617.graph sourceMap3884=true := by decide +kernel
theorem fusedMap3884_checked : acceptsGraphIso
    (fused (graph core3884) (root 8) 1 4) DegreeTwoThreeSpectrum4093.graph fusedMap3884=true := by decide +kernel
theorem certified3884 : Certified (graph core3884) (root 8) 1 4 :=
  of_native_maps core3884 DegreeTwoThreeSpectrum4617.graph DegreeTwoThreeSpectrum4093.graph
    sourceMap3884 fusedMap3884 sourceMap3884_checked fusedMap3884_checked
    DegreeTwoThreeFiniteComparisons.comparison3884
#print axioms sourceMap3884_checked
#print axioms fusedMap3884_checked
#print axioms certified3884
def sourceMap3884swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3884swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3884swap_checked : acceptsGraphIso
    (source (graph core3884) (root 8) 4 1) DegreeTwoThreeSpectrum4617.graph sourceMap3884swap=true := by decide +kernel
theorem fusedMap3884swap_checked : acceptsGraphIso
    (fused (graph core3884) (root 8) 4 1) DegreeTwoThreeSpectrum4093.graph fusedMap3884swap=true := by decide +kernel
theorem certified3884swap : Certified (graph core3884) (root 8) 4 1 :=
  of_native_maps core3884 DegreeTwoThreeSpectrum4617.graph DegreeTwoThreeSpectrum4093.graph
    sourceMap3884swap fusedMap3884swap sourceMap3884swap_checked fusedMap3884swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3884
#print axioms sourceMap3884swap_checked
#print axioms fusedMap3884swap_checked
#print axioms certified3884swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
