/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1953 : Family 10 := level10.get ⟨1497,by decide⟩
def sourceMap1953 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1953 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 0 2 v)
theorem sourceMap1953_checked : acceptsGraphIso
    (source (graph core1953) (root 10) 0 2) DegreeTwoThreeSpectrum3189.graph sourceMap1953=true := by decide +kernel
theorem fusedMap1953_checked : acceptsGraphIso
    (fused (graph core1953) (root 10) 0 2) DegreeTwoThreeSpectrum3725.graph fusedMap1953=true := by decide +kernel
theorem certified1953 : Certified (graph core1953) (root 10) 0 2 :=
  of_native_maps core1953 DegreeTwoThreeSpectrum3189.graph DegreeTwoThreeSpectrum3725.graph
    sourceMap1953 fusedMap1953 sourceMap1953_checked fusedMap1953_checked
    DegreeTwoThreeFiniteComparisons.comparison1953
#print axioms sourceMap1953_checked
#print axioms fusedMap1953_checked
#print axioms certified1953
def sourceMap1953swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1953swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,9,10,11,12,13,14,5,6,7,8] (fusedLabel 10 2 0 v)
theorem sourceMap1953swap_checked : acceptsGraphIso
    (source (graph core1953) (root 10) 2 0) DegreeTwoThreeSpectrum3189.graph sourceMap1953swap=true := by decide +kernel
theorem fusedMap1953swap_checked : acceptsGraphIso
    (fused (graph core1953) (root 10) 2 0) DegreeTwoThreeSpectrum3725.graph fusedMap1953swap=true := by decide +kernel
theorem certified1953swap : Certified (graph core1953) (root 10) 2 0 :=
  of_native_maps core1953 DegreeTwoThreeSpectrum3189.graph DegreeTwoThreeSpectrum3725.graph
    sourceMap1953swap fusedMap1953swap sourceMap1953swap_checked fusedMap1953swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1953
#print axioms sourceMap1953swap_checked
#print axioms fusedMap1953swap_checked
#print axioms certified1953swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
