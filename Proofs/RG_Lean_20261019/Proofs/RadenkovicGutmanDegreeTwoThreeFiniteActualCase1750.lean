/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1750 : Family 10 := level10.get ⟨1005,by decide⟩
def sourceMap1750 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1750 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1750_checked : acceptsGraphIso
    (source (graph core1750) (root 10) 0 2) DegreeTwoThreeSpectrum3015.graph sourceMap1750=true := by decide +kernel
theorem fusedMap1750_checked : acceptsGraphIso
    (fused (graph core1750) (root 10) 0 2) DegreeTwoThreeSpectrum3016.graph fusedMap1750=true := by decide +kernel
theorem certified1750 : Certified (graph core1750) (root 10) 0 2 :=
  of_native_maps core1750 DegreeTwoThreeSpectrum3015.graph DegreeTwoThreeSpectrum3016.graph
    sourceMap1750 fusedMap1750 sourceMap1750_checked fusedMap1750_checked
    DegreeTwoThreeFiniteComparisons.comparison1750
#print axioms sourceMap1750_checked
#print axioms fusedMap1750_checked
#print axioms certified1750
def sourceMap1750swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1750swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1750swap_checked : acceptsGraphIso
    (source (graph core1750) (root 10) 2 0) DegreeTwoThreeSpectrum3015.graph sourceMap1750swap=true := by decide +kernel
theorem fusedMap1750swap_checked : acceptsGraphIso
    (fused (graph core1750) (root 10) 2 0) DegreeTwoThreeSpectrum3016.graph fusedMap1750swap=true := by decide +kernel
theorem certified1750swap : Certified (graph core1750) (root 10) 2 0 :=
  of_native_maps core1750 DegreeTwoThreeSpectrum3015.graph DegreeTwoThreeSpectrum3016.graph
    sourceMap1750swap fusedMap1750swap sourceMap1750swap_checked fusedMap1750swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1750
#print axioms sourceMap1750swap_checked
#print axioms fusedMap1750swap_checked
#print axioms certified1750swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
