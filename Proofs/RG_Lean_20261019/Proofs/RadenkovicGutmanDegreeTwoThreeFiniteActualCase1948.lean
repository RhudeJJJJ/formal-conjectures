/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1948 : Family 10 := level10.get ⟨1480,by decide⟩
def sourceMap1948 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1948 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1948_checked : acceptsGraphIso
    (source (graph core1948) (root 10) 0 2) DegreeTwoThreeSpectrum3421.graph sourceMap1948=true := by decide +kernel
theorem fusedMap1948_checked : acceptsGraphIso
    (fused (graph core1948) (root 10) 0 2) DegreeTwoThreeSpectrum3720.graph fusedMap1948=true := by decide +kernel
theorem certified1948 : Certified (graph core1948) (root 10) 0 2 :=
  of_native_maps core1948 DegreeTwoThreeSpectrum3421.graph DegreeTwoThreeSpectrum3720.graph
    sourceMap1948 fusedMap1948 sourceMap1948_checked fusedMap1948_checked
    DegreeTwoThreeFiniteComparisons.comparison1948
#print axioms sourceMap1948_checked
#print axioms fusedMap1948_checked
#print axioms certified1948
def sourceMap1948swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1948swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1948swap_checked : acceptsGraphIso
    (source (graph core1948) (root 10) 2 0) DegreeTwoThreeSpectrum3421.graph sourceMap1948swap=true := by decide +kernel
theorem fusedMap1948swap_checked : acceptsGraphIso
    (fused (graph core1948) (root 10) 2 0) DegreeTwoThreeSpectrum3720.graph fusedMap1948swap=true := by decide +kernel
theorem certified1948swap : Certified (graph core1948) (root 10) 2 0 :=
  of_native_maps core1948 DegreeTwoThreeSpectrum3421.graph DegreeTwoThreeSpectrum3720.graph
    sourceMap1948swap fusedMap1948swap sourceMap1948swap_checked fusedMap1948swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1948
#print axioms sourceMap1948swap_checked
#print axioms fusedMap1948swap_checked
#print axioms certified1948swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
