/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1854 : Family 10 := level10.get ⟨1265,by decide⟩
def sourceMap1854 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1854 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1854_checked : acceptsGraphIso
    (source (graph core1854) (root 10) 0 2) DegreeTwoThreeSpectrum3412.graph sourceMap1854=true := by decide +kernel
theorem fusedMap1854_checked : acceptsGraphIso
    (fused (graph core1854) (root 10) 0 2) DegreeTwoThreeSpectrum3416.graph fusedMap1854=true := by decide +kernel
theorem certified1854 : Certified (graph core1854) (root 10) 0 2 :=
  of_native_maps core1854 DegreeTwoThreeSpectrum3412.graph DegreeTwoThreeSpectrum3416.graph
    sourceMap1854 fusedMap1854 sourceMap1854_checked fusedMap1854_checked
    DegreeTwoThreeFiniteComparisons.comparison1854
#print axioms sourceMap1854_checked
#print axioms fusedMap1854_checked
#print axioms certified1854
def sourceMap1854swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1854swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1854swap_checked : acceptsGraphIso
    (source (graph core1854) (root 10) 2 0) DegreeTwoThreeSpectrum3412.graph sourceMap1854swap=true := by decide +kernel
theorem fusedMap1854swap_checked : acceptsGraphIso
    (fused (graph core1854) (root 10) 2 0) DegreeTwoThreeSpectrum3416.graph fusedMap1854swap=true := by decide +kernel
theorem certified1854swap : Certified (graph core1854) (root 10) 2 0 :=
  of_native_maps core1854 DegreeTwoThreeSpectrum3412.graph DegreeTwoThreeSpectrum3416.graph
    sourceMap1854swap fusedMap1854swap sourceMap1854swap_checked fusedMap1854swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1854
#print axioms sourceMap1854swap_checked
#print axioms fusedMap1854swap_checked
#print axioms certified1854swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
