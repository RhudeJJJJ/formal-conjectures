/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1431 : Family 10 := level10.get ⟨9,by decide⟩
def sourceMap1431 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![3,2,1,0,9,10,11,12,13,14,7,8,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap1431 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 0 2 v)
theorem sourceMap1431_checked : acceptsGraphIso
    (source (graph core1431) (root 10) 0 2) DegreeTwoThreeSpectrum2393.graph sourceMap1431=true := by decide +kernel
theorem fusedMap1431_checked : acceptsGraphIso
    (fused (graph core1431) (root 10) 0 2) DegreeTwoThreeSpectrum2312.graph fusedMap1431=true := by decide +kernel
theorem certified1431 : Certified (graph core1431) (root 10) 0 2 :=
  of_native_maps core1431 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap1431 fusedMap1431 sourceMap1431_checked fusedMap1431_checked
    DegreeTwoThreeFiniteComparisons.comparison1431
#print axioms sourceMap1431_checked
#print axioms fusedMap1431_checked
#print axioms certified1431
def sourceMap1431swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,2,1,0,9,10,11,12,13,14,7,4,5,6,8] (sourceLabel 10 2 0 v)
def fusedMap1431swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 2 0 v)
theorem sourceMap1431swap_checked : acceptsGraphIso
    (source (graph core1431) (root 10) 2 0) DegreeTwoThreeSpectrum2393.graph sourceMap1431swap=true := by decide +kernel
theorem fusedMap1431swap_checked : acceptsGraphIso
    (fused (graph core1431) (root 10) 2 0) DegreeTwoThreeSpectrum2312.graph fusedMap1431swap=true := by decide +kernel
theorem certified1431swap : Certified (graph core1431) (root 10) 2 0 :=
  of_native_maps core1431 DegreeTwoThreeSpectrum2393.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap1431swap fusedMap1431swap sourceMap1431swap_checked fusedMap1431swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1431
#print axioms sourceMap1431swap_checked
#print axioms fusedMap1431swap_checked
#print axioms certified1431swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
