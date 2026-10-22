/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1196 : Family 9 := level9.get ⟨33,by decide⟩
def sourceMap1196 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,7,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1196 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1196_checked : acceptsGraphIso
    (source (graph core1196) (root 9) 0 2) DegreeTwoThreeSpectrum1888.graph sourceMap1196=true := by decide +kernel
theorem fusedMap1196_checked : acceptsGraphIso
    (fused (graph core1196) (root 9) 0 2) DegreeTwoThreeSpectrum1732.graph fusedMap1196=true := by decide +kernel
theorem certified1196 : Certified (graph core1196) (root 9) 0 2 :=
  of_native_maps core1196 DegreeTwoThreeSpectrum1888.graph DegreeTwoThreeSpectrum1732.graph
    sourceMap1196 fusedMap1196 sourceMap1196_checked fusedMap1196_checked
    DegreeTwoThreeFiniteComparisons.comparison1196
#print axioms sourceMap1196_checked
#print axioms fusedMap1196_checked
#print axioms certified1196
def sourceMap1196swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,8,9,10,11,12,13,6,3,4,5,7] (sourceLabel 9 2 0 v)
def fusedMap1196swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1196swap_checked : acceptsGraphIso
    (source (graph core1196) (root 9) 2 0) DegreeTwoThreeSpectrum1888.graph sourceMap1196swap=true := by decide +kernel
theorem fusedMap1196swap_checked : acceptsGraphIso
    (fused (graph core1196) (root 9) 2 0) DegreeTwoThreeSpectrum1732.graph fusedMap1196swap=true := by decide +kernel
theorem certified1196swap : Certified (graph core1196) (root 9) 2 0 :=
  of_native_maps core1196 DegreeTwoThreeSpectrum1888.graph DegreeTwoThreeSpectrum1732.graph
    sourceMap1196swap fusedMap1196swap sourceMap1196swap_checked fusedMap1196swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1196
#print axioms sourceMap1196swap_checked
#print axioms fusedMap1196swap_checked
#print axioms certified1196swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
