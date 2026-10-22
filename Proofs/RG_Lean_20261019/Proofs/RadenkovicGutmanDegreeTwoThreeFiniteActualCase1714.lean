/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1714 : Family 10 := level10.get ⟨916,by decide⟩
def sourceMap1714 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1714 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1714_checked : acceptsGraphIso
    (source (graph core1714) (root 10) 0 2) DegreeTwoThreeSpectrum2933.graph sourceMap1714=true := by decide +kernel
theorem fusedMap1714_checked : acceptsGraphIso
    (fused (graph core1714) (root 10) 0 2) DegreeTwoThreeSpectrum2930.graph fusedMap1714=true := by decide +kernel
theorem certified1714 : Certified (graph core1714) (root 10) 0 2 :=
  of_native_maps core1714 DegreeTwoThreeSpectrum2933.graph DegreeTwoThreeSpectrum2930.graph
    sourceMap1714 fusedMap1714 sourceMap1714_checked fusedMap1714_checked
    DegreeTwoThreeFiniteComparisons.comparison1714
#print axioms sourceMap1714_checked
#print axioms fusedMap1714_checked
#print axioms certified1714
def sourceMap1714swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1714swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1714swap_checked : acceptsGraphIso
    (source (graph core1714) (root 10) 2 0) DegreeTwoThreeSpectrum2933.graph sourceMap1714swap=true := by decide +kernel
theorem fusedMap1714swap_checked : acceptsGraphIso
    (fused (graph core1714) (root 10) 2 0) DegreeTwoThreeSpectrum2930.graph fusedMap1714swap=true := by decide +kernel
theorem certified1714swap : Certified (graph core1714) (root 10) 2 0 :=
  of_native_maps core1714 DegreeTwoThreeSpectrum2933.graph DegreeTwoThreeSpectrum2930.graph
    sourceMap1714swap fusedMap1714swap sourceMap1714swap_checked fusedMap1714swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1714
#print axioms sourceMap1714swap_checked
#print axioms fusedMap1714swap_checked
#print axioms certified1714swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
