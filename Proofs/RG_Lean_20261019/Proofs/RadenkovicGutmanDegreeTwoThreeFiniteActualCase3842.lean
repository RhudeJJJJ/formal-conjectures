/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3842 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap3842 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3842 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3842_checked : acceptsGraphIso
    (source (graph core3842) (root 8) 1 4) DegreeTwoThreeSpectrum4532.graph sourceMap3842=true := by decide +kernel
theorem fusedMap3842_checked : acceptsGraphIso
    (fused (graph core3842) (root 8) 1 4) DegreeTwoThreeSpectrum4045.graph fusedMap3842=true := by decide +kernel
theorem certified3842 : Certified (graph core3842) (root 8) 1 4 :=
  of_native_maps core3842 DegreeTwoThreeSpectrum4532.graph DegreeTwoThreeSpectrum4045.graph
    sourceMap3842 fusedMap3842 sourceMap3842_checked fusedMap3842_checked
    DegreeTwoThreeFiniteComparisons.comparison3842
#print axioms sourceMap3842_checked
#print axioms fusedMap3842_checked
#print axioms certified3842
def sourceMap3842swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3842swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3842swap_checked : acceptsGraphIso
    (source (graph core3842) (root 8) 4 1) DegreeTwoThreeSpectrum4532.graph sourceMap3842swap=true := by decide +kernel
theorem fusedMap3842swap_checked : acceptsGraphIso
    (fused (graph core3842) (root 8) 4 1) DegreeTwoThreeSpectrum4045.graph fusedMap3842swap=true := by decide +kernel
theorem certified3842swap : Certified (graph core3842) (root 8) 4 1 :=
  of_native_maps core3842 DegreeTwoThreeSpectrum4532.graph DegreeTwoThreeSpectrum4045.graph
    sourceMap3842swap fusedMap3842swap sourceMap3842swap_checked fusedMap3842swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3842
#print axioms sourceMap3842swap_checked
#print axioms fusedMap3842swap_checked
#print axioms certified3842swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
