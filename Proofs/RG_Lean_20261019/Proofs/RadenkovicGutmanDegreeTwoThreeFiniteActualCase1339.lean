/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1339 : Family 9 := level9.get ⟨454,by decide⟩
def sourceMap1339 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1339 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1339_checked : acceptsGraphIso
    (source (graph core1339) (root 9) 0 2) DegreeTwoThreeSpectrum2135.graph sourceMap1339=true := by decide +kernel
theorem fusedMap1339_checked : acceptsGraphIso
    (fused (graph core1339) (root 9) 0 2) DegreeTwoThreeSpectrum2139.graph fusedMap1339=true := by decide +kernel
theorem certified1339 : Certified (graph core1339) (root 9) 0 2 :=
  of_native_maps core1339 DegreeTwoThreeSpectrum2135.graph DegreeTwoThreeSpectrum2139.graph
    sourceMap1339 fusedMap1339 sourceMap1339_checked fusedMap1339_checked
    DegreeTwoThreeFiniteComparisons.comparison1339
#print axioms sourceMap1339_checked
#print axioms fusedMap1339_checked
#print axioms certified1339
def sourceMap1339swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1339swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1339swap_checked : acceptsGraphIso
    (source (graph core1339) (root 9) 2 0) DegreeTwoThreeSpectrum2135.graph sourceMap1339swap=true := by decide +kernel
theorem fusedMap1339swap_checked : acceptsGraphIso
    (fused (graph core1339) (root 9) 2 0) DegreeTwoThreeSpectrum2139.graph fusedMap1339swap=true := by decide +kernel
theorem certified1339swap : Certified (graph core1339) (root 9) 2 0 :=
  of_native_maps core1339 DegreeTwoThreeSpectrum2135.graph DegreeTwoThreeSpectrum2139.graph
    sourceMap1339swap fusedMap1339swap sourceMap1339swap_checked fusedMap1339swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1339
#print axioms sourceMap1339swap_checked
#print axioms fusedMap1339swap_checked
#print axioms certified1339swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
