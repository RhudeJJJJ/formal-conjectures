/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1226 : Family 9 := level9.get ⟨141,by decide⟩
def sourceMap1226 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1226 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1226_checked : acceptsGraphIso
    (source (graph core1226) (root 9) 0 2) DegreeTwoThreeSpectrum1946.graph sourceMap1226=true := by decide +kernel
theorem fusedMap1226_checked : acceptsGraphIso
    (fused (graph core1226) (root 9) 0 2) DegreeTwoThreeSpectrum1741.graph fusedMap1226=true := by decide +kernel
theorem certified1226 : Certified (graph core1226) (root 9) 0 2 :=
  of_native_maps core1226 DegreeTwoThreeSpectrum1946.graph DegreeTwoThreeSpectrum1741.graph
    sourceMap1226 fusedMap1226 sourceMap1226_checked fusedMap1226_checked
    DegreeTwoThreeFiniteComparisons.comparison1226
#print axioms sourceMap1226_checked
#print axioms fusedMap1226_checked
#print axioms certified1226
def sourceMap1226swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1226swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1226swap_checked : acceptsGraphIso
    (source (graph core1226) (root 9) 2 0) DegreeTwoThreeSpectrum1946.graph sourceMap1226swap=true := by decide +kernel
theorem fusedMap1226swap_checked : acceptsGraphIso
    (fused (graph core1226) (root 9) 2 0) DegreeTwoThreeSpectrum1741.graph fusedMap1226swap=true := by decide +kernel
theorem certified1226swap : Certified (graph core1226) (root 9) 2 0 :=
  of_native_maps core1226 DegreeTwoThreeSpectrum1946.graph DegreeTwoThreeSpectrum1741.graph
    sourceMap1226swap fusedMap1226swap sourceMap1226swap_checked fusedMap1226swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1226
#print axioms sourceMap1226swap_checked
#print axioms fusedMap1226swap_checked
#print axioms certified1226swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
