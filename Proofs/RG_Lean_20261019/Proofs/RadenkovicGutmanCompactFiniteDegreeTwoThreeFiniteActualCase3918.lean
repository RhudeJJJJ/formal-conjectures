/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3918 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap3918 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3918 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3918_checked : acceptsGraphIso
    (source (graph core3918) (root 8) 1 4) DegreeTwoThreeSpectrum4901.graph sourceMap3918=true := by decide +kernel
theorem fusedMap3918_checked : acceptsGraphIso
    (fused (graph core3918) (root 8) 1 4) DegreeTwoThreeSpectrum4564.graph fusedMap3918=true := by decide +kernel
theorem certified3918 : Certified (graph core3918) (root 8) 1 4 :=
  of_native_maps core3918 DegreeTwoThreeSpectrum4901.graph DegreeTwoThreeSpectrum4564.graph
    sourceMap3918 fusedMap3918 sourceMap3918_checked fusedMap3918_checked
    DegreeTwoThreeFiniteComparisons.comparison3918
#print axioms sourceMap3918_checked
#print axioms fusedMap3918_checked
#print axioms certified3918
def sourceMap3918swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,12,13,14,15,10,11] (sourceLabel 8 4 1 v)
def fusedMap3918swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3918swap_checked : acceptsGraphIso
    (source (graph core3918) (root 8) 4 1) DegreeTwoThreeSpectrum4901.graph sourceMap3918swap=true := by decide +kernel
theorem fusedMap3918swap_checked : acceptsGraphIso
    (fused (graph core3918) (root 8) 4 1) DegreeTwoThreeSpectrum4564.graph fusedMap3918swap=true := by decide +kernel
theorem certified3918swap : Certified (graph core3918) (root 8) 4 1 :=
  of_native_maps core3918 DegreeTwoThreeSpectrum4901.graph DegreeTwoThreeSpectrum4564.graph
    sourceMap3918swap fusedMap3918swap sourceMap3918swap_checked fusedMap3918swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3918
#print axioms sourceMap3918swap_checked
#print axioms fusedMap3918swap_checked
#print axioms certified3918swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
