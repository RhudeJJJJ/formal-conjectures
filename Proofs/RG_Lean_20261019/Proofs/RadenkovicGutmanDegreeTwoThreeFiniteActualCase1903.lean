/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1903 : Family 10 := level10.get ⟨1378,by decide⟩
def sourceMap1903 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1903 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1903_checked : acceptsGraphIso
    (source (graph core1903) (root 10) 0 2) DegreeTwoThreeSpectrum3586.graph sourceMap1903=true := by decide +kernel
theorem fusedMap1903_checked : acceptsGraphIso
    (fused (graph core1903) (root 10) 0 2) DegreeTwoThreeSpectrum3583.graph fusedMap1903=true := by decide +kernel
theorem certified1903 : Certified (graph core1903) (root 10) 0 2 :=
  of_native_maps core1903 DegreeTwoThreeSpectrum3586.graph DegreeTwoThreeSpectrum3583.graph
    sourceMap1903 fusedMap1903 sourceMap1903_checked fusedMap1903_checked
    DegreeTwoThreeFiniteComparisons.comparison1903
#print axioms sourceMap1903_checked
#print axioms fusedMap1903_checked
#print axioms certified1903
def sourceMap1903swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1903swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1903swap_checked : acceptsGraphIso
    (source (graph core1903) (root 10) 2 0) DegreeTwoThreeSpectrum3586.graph sourceMap1903swap=true := by decide +kernel
theorem fusedMap1903swap_checked : acceptsGraphIso
    (fused (graph core1903) (root 10) 2 0) DegreeTwoThreeSpectrum3583.graph fusedMap1903swap=true := by decide +kernel
theorem certified1903swap : Certified (graph core1903) (root 10) 2 0 :=
  of_native_maps core1903 DegreeTwoThreeSpectrum3586.graph DegreeTwoThreeSpectrum3583.graph
    sourceMap1903swap fusedMap1903swap sourceMap1903swap_checked fusedMap1903swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1903
#print axioms sourceMap1903swap_checked
#print axioms fusedMap1903swap_checked
#print axioms certified1903swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
