/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1274 : Family 9 := level9.get ⟨284,by decide⟩
def sourceMap1274 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,8,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1274 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1274_checked : acceptsGraphIso
    (source (graph core1274) (root 9) 0 2) DegreeTwoThreeSpectrum2199.graph sourceMap1274=true := by decide +kernel
theorem fusedMap1274_checked : acceptsGraphIso
    (fused (graph core1274) (root 9) 0 2) DegreeTwoThreeSpectrum1898.graph fusedMap1274=true := by decide +kernel
theorem certified1274 : Certified (graph core1274) (root 9) 0 2 :=
  of_native_maps core1274 DegreeTwoThreeSpectrum2199.graph DegreeTwoThreeSpectrum1898.graph
    sourceMap1274 fusedMap1274 sourceMap1274_checked fusedMap1274_checked
    DegreeTwoThreeFiniteComparisons.comparison1274
#print axioms sourceMap1274_checked
#print axioms fusedMap1274_checked
#print axioms certified1274
def sourceMap1274swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,5,6,7,2,3,4,8] (sourceLabel 9 2 0 v)
def fusedMap1274swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1274swap_checked : acceptsGraphIso
    (source (graph core1274) (root 9) 2 0) DegreeTwoThreeSpectrum2199.graph sourceMap1274swap=true := by decide +kernel
theorem fusedMap1274swap_checked : acceptsGraphIso
    (fused (graph core1274) (root 9) 2 0) DegreeTwoThreeSpectrum1898.graph fusedMap1274swap=true := by decide +kernel
theorem certified1274swap : Certified (graph core1274) (root 9) 2 0 :=
  of_native_maps core1274 DegreeTwoThreeSpectrum2199.graph DegreeTwoThreeSpectrum1898.graph
    sourceMap1274swap fusedMap1274swap sourceMap1274swap_checked fusedMap1274swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1274
#print axioms sourceMap1274swap_checked
#print axioms fusedMap1274swap_checked
#print axioms certified1274swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
