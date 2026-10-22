/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1815 : Family 10 := level10.get ⟨1168,by decide⟩
def sourceMap1815 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1815 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1815_checked : acceptsGraphIso
    (source (graph core1815) (root 10) 0 2) DegreeTwoThreeSpectrum3266.graph sourceMap1815=true := by decide +kernel
theorem fusedMap1815_checked : acceptsGraphIso
    (fused (graph core1815) (root 10) 0 2) DegreeTwoThreeSpectrum3276.graph fusedMap1815=true := by decide +kernel
theorem certified1815 : Certified (graph core1815) (root 10) 0 2 :=
  of_native_maps core1815 DegreeTwoThreeSpectrum3266.graph DegreeTwoThreeSpectrum3276.graph
    sourceMap1815 fusedMap1815 sourceMap1815_checked fusedMap1815_checked
    DegreeTwoThreeFiniteComparisons.comparison1815
#print axioms sourceMap1815_checked
#print axioms fusedMap1815_checked
#print axioms certified1815
def sourceMap1815swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1815swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1815swap_checked : acceptsGraphIso
    (source (graph core1815) (root 10) 2 0) DegreeTwoThreeSpectrum3266.graph sourceMap1815swap=true := by decide +kernel
theorem fusedMap1815swap_checked : acceptsGraphIso
    (fused (graph core1815) (root 10) 2 0) DegreeTwoThreeSpectrum3276.graph fusedMap1815swap=true := by decide +kernel
theorem certified1815swap : Certified (graph core1815) (root 10) 2 0 :=
  of_native_maps core1815 DegreeTwoThreeSpectrum3266.graph DegreeTwoThreeSpectrum3276.graph
    sourceMap1815swap fusedMap1815swap sourceMap1815swap_checked fusedMap1815swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1815
#print axioms sourceMap1815swap_checked
#print axioms fusedMap1815swap_checked
#print axioms certified1815swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
