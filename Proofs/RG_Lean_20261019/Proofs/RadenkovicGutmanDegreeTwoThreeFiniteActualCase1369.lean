/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1369 : Family 9 := level9.get ⟨519,by decide⟩
def sourceMap1369 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1369 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1369_checked : acceptsGraphIso
    (source (graph core1369) (root 9) 0 2) DegreeTwoThreeSpectrum2142.graph sourceMap1369=true := by decide +kernel
theorem fusedMap1369_checked : acceptsGraphIso
    (fused (graph core1369) (root 9) 0 2) DegreeTwoThreeSpectrum2231.graph fusedMap1369=true := by decide +kernel
theorem certified1369 : Certified (graph core1369) (root 9) 0 2 :=
  of_native_maps core1369 DegreeTwoThreeSpectrum2142.graph DegreeTwoThreeSpectrum2231.graph
    sourceMap1369 fusedMap1369 sourceMap1369_checked fusedMap1369_checked
    DegreeTwoThreeFiniteComparisons.comparison1369
#print axioms sourceMap1369_checked
#print axioms fusedMap1369_checked
#print axioms certified1369
def sourceMap1369swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1369swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1369swap_checked : acceptsGraphIso
    (source (graph core1369) (root 9) 2 0) DegreeTwoThreeSpectrum2142.graph sourceMap1369swap=true := by decide +kernel
theorem fusedMap1369swap_checked : acceptsGraphIso
    (fused (graph core1369) (root 9) 2 0) DegreeTwoThreeSpectrum2231.graph fusedMap1369swap=true := by decide +kernel
theorem certified1369swap : Certified (graph core1369) (root 9) 2 0 :=
  of_native_maps core1369 DegreeTwoThreeSpectrum2142.graph DegreeTwoThreeSpectrum2231.graph
    sourceMap1369swap fusedMap1369swap sourceMap1369swap_checked fusedMap1369swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1369
#print axioms sourceMap1369swap_checked
#print axioms fusedMap1369swap_checked
#print axioms certified1369swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
