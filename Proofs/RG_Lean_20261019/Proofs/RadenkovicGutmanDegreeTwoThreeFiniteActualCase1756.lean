/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1756 : Family 10 := level10.get ⟨1023,by decide⟩
def sourceMap1756 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1756 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1756_checked : acceptsGraphIso
    (source (graph core1756) (root 10) 0 2) DegreeTwoThreeSpectrum3046.graph sourceMap1756=true := by decide +kernel
theorem fusedMap1756_checked : acceptsGraphIso
    (fused (graph core1756) (root 10) 0 2) DegreeTwoThreeSpectrum3047.graph fusedMap1756=true := by decide +kernel
theorem certified1756 : Certified (graph core1756) (root 10) 0 2 :=
  of_native_maps core1756 DegreeTwoThreeSpectrum3046.graph DegreeTwoThreeSpectrum3047.graph
    sourceMap1756 fusedMap1756 sourceMap1756_checked fusedMap1756_checked
    DegreeTwoThreeFiniteComparisons.comparison1756
#print axioms sourceMap1756_checked
#print axioms fusedMap1756_checked
#print axioms certified1756
def sourceMap1756swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1756swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1756swap_checked : acceptsGraphIso
    (source (graph core1756) (root 10) 2 0) DegreeTwoThreeSpectrum3046.graph sourceMap1756swap=true := by decide +kernel
theorem fusedMap1756swap_checked : acceptsGraphIso
    (fused (graph core1756) (root 10) 2 0) DegreeTwoThreeSpectrum3047.graph fusedMap1756swap=true := by decide +kernel
theorem certified1756swap : Certified (graph core1756) (root 10) 2 0 :=
  of_native_maps core1756 DegreeTwoThreeSpectrum3046.graph DegreeTwoThreeSpectrum3047.graph
    sourceMap1756swap fusedMap1756swap sourceMap1756swap_checked fusedMap1756swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1756
#print axioms sourceMap1756swap_checked
#print axioms fusedMap1756swap_checked
#print axioms certified1756swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
