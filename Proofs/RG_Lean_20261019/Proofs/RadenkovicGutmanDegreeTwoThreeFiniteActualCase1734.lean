/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1734 : Family 10 := level10.get ⟨963,by decide⟩
def sourceMap1734 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1734 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1734_checked : acceptsGraphIso
    (source (graph core1734) (root 10) 0 2) DegreeTwoThreeSpectrum3661.graph sourceMap1734=true := by decide +kernel
theorem fusedMap1734_checked : acceptsGraphIso
    (fused (graph core1734) (root 10) 0 2) DegreeTwoThreeSpectrum2969.graph fusedMap1734=true := by decide +kernel
theorem certified1734 : Certified (graph core1734) (root 10) 0 2 :=
  of_native_maps core1734 DegreeTwoThreeSpectrum3661.graph DegreeTwoThreeSpectrum2969.graph
    sourceMap1734 fusedMap1734 sourceMap1734_checked fusedMap1734_checked
    DegreeTwoThreeFiniteComparisons.comparison1734
#print axioms sourceMap1734_checked
#print axioms fusedMap1734_checked
#print axioms certified1734
def sourceMap1734swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1734swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1734swap_checked : acceptsGraphIso
    (source (graph core1734) (root 10) 2 0) DegreeTwoThreeSpectrum3661.graph sourceMap1734swap=true := by decide +kernel
theorem fusedMap1734swap_checked : acceptsGraphIso
    (fused (graph core1734) (root 10) 2 0) DegreeTwoThreeSpectrum2969.graph fusedMap1734swap=true := by decide +kernel
theorem certified1734swap : Certified (graph core1734) (root 10) 2 0 :=
  of_native_maps core1734 DegreeTwoThreeSpectrum3661.graph DegreeTwoThreeSpectrum2969.graph
    sourceMap1734swap fusedMap1734swap sourceMap1734swap_checked fusedMap1734swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1734
#print axioms sourceMap1734swap_checked
#print axioms fusedMap1734swap_checked
#print axioms certified1734swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
