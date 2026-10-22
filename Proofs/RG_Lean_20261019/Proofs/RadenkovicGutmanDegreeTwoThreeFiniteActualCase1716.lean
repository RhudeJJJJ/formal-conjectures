/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1716 : Family 10 := level10.get ⟨918,by decide⟩
def sourceMap1716 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1716 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1716_checked : acceptsGraphIso
    (source (graph core1716) (root 10) 0 2) DegreeTwoThreeSpectrum3537.graph sourceMap1716=true := by decide +kernel
theorem fusedMap1716_checked : acceptsGraphIso
    (fused (graph core1716) (root 10) 0 2) DegreeTwoThreeSpectrum2932.graph fusedMap1716=true := by decide +kernel
theorem certified1716 : Certified (graph core1716) (root 10) 0 2 :=
  of_native_maps core1716 DegreeTwoThreeSpectrum3537.graph DegreeTwoThreeSpectrum2932.graph
    sourceMap1716 fusedMap1716 sourceMap1716_checked fusedMap1716_checked
    DegreeTwoThreeFiniteComparisons.comparison1716
#print axioms sourceMap1716_checked
#print axioms fusedMap1716_checked
#print axioms certified1716
def sourceMap1716swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1716swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1716swap_checked : acceptsGraphIso
    (source (graph core1716) (root 10) 2 0) DegreeTwoThreeSpectrum3537.graph sourceMap1716swap=true := by decide +kernel
theorem fusedMap1716swap_checked : acceptsGraphIso
    (fused (graph core1716) (root 10) 2 0) DegreeTwoThreeSpectrum2932.graph fusedMap1716swap=true := by decide +kernel
theorem certified1716swap : Certified (graph core1716) (root 10) 2 0 :=
  of_native_maps core1716 DegreeTwoThreeSpectrum3537.graph DegreeTwoThreeSpectrum2932.graph
    sourceMap1716swap fusedMap1716swap sourceMap1716swap_checked fusedMap1716swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1716
#print axioms sourceMap1716swap_checked
#print axioms fusedMap1716swap_checked
#print axioms certified1716swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
