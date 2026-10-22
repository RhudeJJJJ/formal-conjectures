/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1711 : Family 10 := level10.get ⟨910,by decide⟩
def sourceMap1711 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1711 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1711_checked : acceptsGraphIso
    (source (graph core1711) (root 10) 0 2) DegreeTwoThreeSpectrum3682.graph sourceMap1711=true := by decide +kernel
theorem fusedMap1711_checked : acceptsGraphIso
    (fused (graph core1711) (root 10) 0 2) DegreeTwoThreeSpectrum2923.graph fusedMap1711=true := by decide +kernel
theorem certified1711 : Certified (graph core1711) (root 10) 0 2 :=
  of_native_maps core1711 DegreeTwoThreeSpectrum3682.graph DegreeTwoThreeSpectrum2923.graph
    sourceMap1711 fusedMap1711 sourceMap1711_checked fusedMap1711_checked
    DegreeTwoThreeFiniteComparisons.comparison1711
#print axioms sourceMap1711_checked
#print axioms fusedMap1711_checked
#print axioms certified1711
def sourceMap1711swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1711swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1711swap_checked : acceptsGraphIso
    (source (graph core1711) (root 10) 2 0) DegreeTwoThreeSpectrum3682.graph sourceMap1711swap=true := by decide +kernel
theorem fusedMap1711swap_checked : acceptsGraphIso
    (fused (graph core1711) (root 10) 2 0) DegreeTwoThreeSpectrum2923.graph fusedMap1711swap=true := by decide +kernel
theorem certified1711swap : Certified (graph core1711) (root 10) 2 0 :=
  of_native_maps core1711 DegreeTwoThreeSpectrum3682.graph DegreeTwoThreeSpectrum2923.graph
    sourceMap1711swap fusedMap1711swap sourceMap1711swap_checked fusedMap1711swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1711
#print axioms sourceMap1711swap_checked
#print axioms fusedMap1711swap_checked
#print axioms certified1711swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
