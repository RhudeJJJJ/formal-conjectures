/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1783 : Family 10 := level10.get ⟨1087,by decide⟩
def sourceMap1783 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1783 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1783_checked : acceptsGraphIso
    (source (graph core1783) (root 10) 0 2) DegreeTwoThreeSpectrum3144.graph sourceMap1783=true := by decide +kernel
theorem fusedMap1783_checked : acceptsGraphIso
    (fused (graph core1783) (root 10) 0 2) DegreeTwoThreeSpectrum3154.graph fusedMap1783=true := by decide +kernel
theorem certified1783 : Certified (graph core1783) (root 10) 0 2 :=
  of_native_maps core1783 DegreeTwoThreeSpectrum3144.graph DegreeTwoThreeSpectrum3154.graph
    sourceMap1783 fusedMap1783 sourceMap1783_checked fusedMap1783_checked
    DegreeTwoThreeFiniteComparisons.comparison1783
#print axioms sourceMap1783_checked
#print axioms fusedMap1783_checked
#print axioms certified1783
def sourceMap1783swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1783swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1783swap_checked : acceptsGraphIso
    (source (graph core1783) (root 10) 2 0) DegreeTwoThreeSpectrum3144.graph sourceMap1783swap=true := by decide +kernel
theorem fusedMap1783swap_checked : acceptsGraphIso
    (fused (graph core1783) (root 10) 2 0) DegreeTwoThreeSpectrum3154.graph fusedMap1783swap=true := by decide +kernel
theorem certified1783swap : Certified (graph core1783) (root 10) 2 0 :=
  of_native_maps core1783 DegreeTwoThreeSpectrum3144.graph DegreeTwoThreeSpectrum3154.graph
    sourceMap1783swap fusedMap1783swap sourceMap1783swap_checked fusedMap1783swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1783
#print axioms sourceMap1783swap_checked
#print axioms fusedMap1783swap_checked
#print axioms certified1783swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
