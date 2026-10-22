/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1963 : Family 10 := level10.get ⟨1536,by decide⟩
def sourceMap1963 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1963 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1963_checked : acceptsGraphIso
    (source (graph core1963) (root 10) 0 2) DegreeTwoThreeSpectrum3744.graph sourceMap1963=true := by decide +kernel
theorem fusedMap1963_checked : acceptsGraphIso
    (fused (graph core1963) (root 10) 0 2) DegreeTwoThreeSpectrum3009.graph fusedMap1963=true := by decide +kernel
theorem certified1963 : Certified (graph core1963) (root 10) 0 2 :=
  of_native_maps core1963 DegreeTwoThreeSpectrum3744.graph DegreeTwoThreeSpectrum3009.graph
    sourceMap1963 fusedMap1963 sourceMap1963_checked fusedMap1963_checked
    DegreeTwoThreeFiniteComparisons.comparison1963
#print axioms sourceMap1963_checked
#print axioms fusedMap1963_checked
#print axioms certified1963
def sourceMap1963swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1963swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1963swap_checked : acceptsGraphIso
    (source (graph core1963) (root 10) 2 0) DegreeTwoThreeSpectrum3744.graph sourceMap1963swap=true := by decide +kernel
theorem fusedMap1963swap_checked : acceptsGraphIso
    (fused (graph core1963) (root 10) 2 0) DegreeTwoThreeSpectrum3009.graph fusedMap1963swap=true := by decide +kernel
theorem certified1963swap : Certified (graph core1963) (root 10) 2 0 :=
  of_native_maps core1963 DegreeTwoThreeSpectrum3744.graph DegreeTwoThreeSpectrum3009.graph
    sourceMap1963swap fusedMap1963swap sourceMap1963swap_checked fusedMap1963swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1963
#print axioms sourceMap1963swap_checked
#print axioms fusedMap1963swap_checked
#print axioms certified1963swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
