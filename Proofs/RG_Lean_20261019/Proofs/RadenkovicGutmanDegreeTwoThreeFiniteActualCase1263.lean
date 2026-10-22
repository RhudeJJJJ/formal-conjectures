/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1263 : Family 9 := level9.get ⟨257,by decide⟩
def sourceMap1263 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1263 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1263_checked : acceptsGraphIso
    (source (graph core1263) (root 9) 0 2) DegreeTwoThreeSpectrum2202.graph sourceMap1263=true := by decide +kernel
theorem fusedMap1263_checked : acceptsGraphIso
    (fused (graph core1263) (root 9) 0 2) DegreeTwoThreeSpectrum1864.graph fusedMap1263=true := by decide +kernel
theorem certified1263 : Certified (graph core1263) (root 9) 0 2 :=
  of_native_maps core1263 DegreeTwoThreeSpectrum2202.graph DegreeTwoThreeSpectrum1864.graph
    sourceMap1263 fusedMap1263 sourceMap1263_checked fusedMap1263_checked
    DegreeTwoThreeFiniteComparisons.comparison1263
#print axioms sourceMap1263_checked
#print axioms fusedMap1263_checked
#print axioms certified1263
def sourceMap1263swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1263swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1263swap_checked : acceptsGraphIso
    (source (graph core1263) (root 9) 2 0) DegreeTwoThreeSpectrum2202.graph sourceMap1263swap=true := by decide +kernel
theorem fusedMap1263swap_checked : acceptsGraphIso
    (fused (graph core1263) (root 9) 2 0) DegreeTwoThreeSpectrum1864.graph fusedMap1263swap=true := by decide +kernel
theorem certified1263swap : Certified (graph core1263) (root 9) 2 0 :=
  of_native_maps core1263 DegreeTwoThreeSpectrum2202.graph DegreeTwoThreeSpectrum1864.graph
    sourceMap1263swap fusedMap1263swap sourceMap1263swap_checked fusedMap1263swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1263
#print axioms sourceMap1263swap_checked
#print axioms fusedMap1263swap_checked
#print axioms certified1263swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
