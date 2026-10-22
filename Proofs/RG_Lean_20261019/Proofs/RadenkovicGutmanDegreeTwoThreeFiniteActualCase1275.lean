/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1275 : Family 9 := level9.get ⟨291,by decide⟩
def sourceMap1275 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1275 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1275_checked : acceptsGraphIso
    (source (graph core1275) (root 9) 0 2) DegreeTwoThreeSpectrum2225.graph sourceMap1275=true := by decide +kernel
theorem fusedMap1275_checked : acceptsGraphIso
    (fused (graph core1275) (root 9) 0 2) DegreeTwoThreeSpectrum1906.graph fusedMap1275=true := by decide +kernel
theorem certified1275 : Certified (graph core1275) (root 9) 0 2 :=
  of_native_maps core1275 DegreeTwoThreeSpectrum2225.graph DegreeTwoThreeSpectrum1906.graph
    sourceMap1275 fusedMap1275 sourceMap1275_checked fusedMap1275_checked
    DegreeTwoThreeFiniteComparisons.comparison1275
#print axioms sourceMap1275_checked
#print axioms fusedMap1275_checked
#print axioms certified1275
def sourceMap1275swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1275swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1275swap_checked : acceptsGraphIso
    (source (graph core1275) (root 9) 2 0) DegreeTwoThreeSpectrum2225.graph sourceMap1275swap=true := by decide +kernel
theorem fusedMap1275swap_checked : acceptsGraphIso
    (fused (graph core1275) (root 9) 2 0) DegreeTwoThreeSpectrum1906.graph fusedMap1275swap=true := by decide +kernel
theorem certified1275swap : Certified (graph core1275) (root 9) 2 0 :=
  of_native_maps core1275 DegreeTwoThreeSpectrum2225.graph DegreeTwoThreeSpectrum1906.graph
    sourceMap1275swap fusedMap1275swap sourceMap1275swap_checked fusedMap1275swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1275
#print axioms sourceMap1275swap_checked
#print axioms fusedMap1275swap_checked
#print axioms certified1275swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
