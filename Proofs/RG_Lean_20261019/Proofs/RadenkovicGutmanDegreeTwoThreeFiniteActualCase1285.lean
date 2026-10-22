/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1285 : Family 9 := level9.get ⟨310,by decide⟩
def sourceMap1285 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,2,3,4,5,9,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1285 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 0 2 v)
theorem sourceMap1285_checked : acceptsGraphIso
    (source (graph core1285) (root 9) 0 2) DegreeTwoThreeSpectrum2143.graph sourceMap1285=true := by decide +kernel
theorem fusedMap1285_checked : acceptsGraphIso
    (fused (graph core1285) (root 9) 0 2) DegreeTwoThreeSpectrum1904.graph fusedMap1285=true := by decide +kernel
theorem certified1285 : Certified (graph core1285) (root 9) 0 2 :=
  of_native_maps core1285 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1904.graph
    sourceMap1285 fusedMap1285 sourceMap1285_checked fusedMap1285_checked
    DegreeTwoThreeFiniteComparisons.comparison1285
#print axioms sourceMap1285_checked
#print axioms fusedMap1285_checked
#print axioms certified1285
def sourceMap1285swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,10,11,12,13,2,3,4,5,6,7,8,9] (sourceLabel 9 2 0 v)
def fusedMap1285swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,5,6,7,8,1,2,3,4] (fusedLabel 9 2 0 v)
theorem sourceMap1285swap_checked : acceptsGraphIso
    (source (graph core1285) (root 9) 2 0) DegreeTwoThreeSpectrum2143.graph sourceMap1285swap=true := by decide +kernel
theorem fusedMap1285swap_checked : acceptsGraphIso
    (fused (graph core1285) (root 9) 2 0) DegreeTwoThreeSpectrum1904.graph fusedMap1285swap=true := by decide +kernel
theorem certified1285swap : Certified (graph core1285) (root 9) 2 0 :=
  of_native_maps core1285 DegreeTwoThreeSpectrum2143.graph DegreeTwoThreeSpectrum1904.graph
    sourceMap1285swap fusedMap1285swap sourceMap1285swap_checked fusedMap1285swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1285
#print axioms sourceMap1285swap_checked
#print axioms fusedMap1285swap_checked
#print axioms certified1285swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
