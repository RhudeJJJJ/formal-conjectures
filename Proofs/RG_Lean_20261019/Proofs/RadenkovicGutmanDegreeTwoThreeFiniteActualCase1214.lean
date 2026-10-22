/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1214 : Family 9 := level9.get ⟨106,by decide⟩
def sourceMap1214 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1214 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1214_checked : acceptsGraphIso
    (source (graph core1214) (root 9) 0 2) DegreeTwoThreeSpectrum1884.graph sourceMap1214=true := by decide +kernel
theorem fusedMap1214_checked : acceptsGraphIso
    (fused (graph core1214) (root 9) 0 2) DegreeTwoThreeSpectrum1896.graph fusedMap1214=true := by decide +kernel
theorem certified1214 : Certified (graph core1214) (root 9) 0 2 :=
  of_native_maps core1214 DegreeTwoThreeSpectrum1884.graph DegreeTwoThreeSpectrum1896.graph
    sourceMap1214 fusedMap1214 sourceMap1214_checked fusedMap1214_checked
    DegreeTwoThreeFiniteComparisons.comparison1214
#print axioms sourceMap1214_checked
#print axioms fusedMap1214_checked
#print axioms certified1214
def sourceMap1214swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1214swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1214swap_checked : acceptsGraphIso
    (source (graph core1214) (root 9) 2 0) DegreeTwoThreeSpectrum1884.graph sourceMap1214swap=true := by decide +kernel
theorem fusedMap1214swap_checked : acceptsGraphIso
    (fused (graph core1214) (root 9) 2 0) DegreeTwoThreeSpectrum1896.graph fusedMap1214swap=true := by decide +kernel
theorem certified1214swap : Certified (graph core1214) (root 9) 2 0 :=
  of_native_maps core1214 DegreeTwoThreeSpectrum1884.graph DegreeTwoThreeSpectrum1896.graph
    sourceMap1214swap fusedMap1214swap sourceMap1214swap_checked fusedMap1214swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1214
#print axioms sourceMap1214swap_checked
#print axioms fusedMap1214swap_checked
#print axioms certified1214swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
