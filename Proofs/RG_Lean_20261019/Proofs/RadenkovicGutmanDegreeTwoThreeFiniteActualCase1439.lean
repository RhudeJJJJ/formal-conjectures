/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1439 : Family 10 := level10.get ⟨51,by decide⟩
def sourceMap1439 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,8,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1439 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,7,8,3,4,5,6] (fusedLabel 10 0 2 v)
theorem sourceMap1439_checked : acceptsGraphIso
    (source (graph core1439) (root 10) 0 2) DegreeTwoThreeSpectrum2383.graph sourceMap1439=true := by decide +kernel
theorem fusedMap1439_checked : acceptsGraphIso
    (fused (graph core1439) (root 10) 0 2) DegreeTwoThreeSpectrum2414.graph fusedMap1439=true := by decide +kernel
theorem certified1439 : Certified (graph core1439) (root 10) 0 2 :=
  of_native_maps core1439 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap1439 fusedMap1439 sourceMap1439_checked fusedMap1439_checked
    DegreeTwoThreeFiniteComparisons.comparison1439
#print axioms sourceMap1439_checked
#print axioms fusedMap1439_checked
#print axioms certified1439
def sourceMap1439swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,3,4,5,8] (sourceLabel 10 2 0 v)
def fusedMap1439swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,7,8,3,4,5,6] (fusedLabel 10 2 0 v)
theorem sourceMap1439swap_checked : acceptsGraphIso
    (source (graph core1439) (root 10) 2 0) DegreeTwoThreeSpectrum2383.graph sourceMap1439swap=true := by decide +kernel
theorem fusedMap1439swap_checked : acceptsGraphIso
    (fused (graph core1439) (root 10) 2 0) DegreeTwoThreeSpectrum2414.graph fusedMap1439swap=true := by decide +kernel
theorem certified1439swap : Certified (graph core1439) (root 10) 2 0 :=
  of_native_maps core1439 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2414.graph
    sourceMap1439swap fusedMap1439swap sourceMap1439swap_checked fusedMap1439swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1439
#print axioms sourceMap1439swap_checked
#print axioms fusedMap1439swap_checked
#print axioms certified1439swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
