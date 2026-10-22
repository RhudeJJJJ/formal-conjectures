/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1218 : Family 9 := level9.get ⟨119,by decide⟩
def sourceMap1218 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1218 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1218_checked : acceptsGraphIso
    (source (graph core1218) (root 9) 0 2) DegreeTwoThreeSpectrum1887.graph sourceMap1218=true := by decide +kernel
theorem fusedMap1218_checked : acceptsGraphIso
    (fused (graph core1218) (root 9) 0 2) DegreeTwoThreeSpectrum1920.graph fusedMap1218=true := by decide +kernel
theorem certified1218 : Certified (graph core1218) (root 9) 0 2 :=
  of_native_maps core1218 DegreeTwoThreeSpectrum1887.graph DegreeTwoThreeSpectrum1920.graph
    sourceMap1218 fusedMap1218 sourceMap1218_checked fusedMap1218_checked
    DegreeTwoThreeFiniteComparisons.comparison1218
#print axioms sourceMap1218_checked
#print axioms fusedMap1218_checked
#print axioms certified1218
def sourceMap1218swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1218swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1218swap_checked : acceptsGraphIso
    (source (graph core1218) (root 9) 2 0) DegreeTwoThreeSpectrum1887.graph sourceMap1218swap=true := by decide +kernel
theorem fusedMap1218swap_checked : acceptsGraphIso
    (fused (graph core1218) (root 9) 2 0) DegreeTwoThreeSpectrum1920.graph fusedMap1218swap=true := by decide +kernel
theorem certified1218swap : Certified (graph core1218) (root 9) 2 0 :=
  of_native_maps core1218 DegreeTwoThreeSpectrum1887.graph DegreeTwoThreeSpectrum1920.graph
    sourceMap1218swap fusedMap1218swap sourceMap1218swap_checked fusedMap1218swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1218
#print axioms sourceMap1218swap_checked
#print axioms fusedMap1218swap_checked
#print axioms certified1218swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
