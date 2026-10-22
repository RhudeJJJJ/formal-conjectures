/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1866 : Family 10 := level10.get ⟨1290,by decide⟩
def sourceMap1866 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1866 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1866_checked : acceptsGraphIso
    (source (graph core1866) (root 10) 0 2) DegreeTwoThreeSpectrum3446.graph sourceMap1866=true := by decide +kernel
theorem fusedMap1866_checked : acceptsGraphIso
    (fused (graph core1866) (root 10) 0 2) DegreeTwoThreeSpectrum3456.graph fusedMap1866=true := by decide +kernel
theorem certified1866 : Certified (graph core1866) (root 10) 0 2 :=
  of_native_maps core1866 DegreeTwoThreeSpectrum3446.graph DegreeTwoThreeSpectrum3456.graph
    sourceMap1866 fusedMap1866 sourceMap1866_checked fusedMap1866_checked
    DegreeTwoThreeFiniteComparisons.comparison1866
#print axioms sourceMap1866_checked
#print axioms fusedMap1866_checked
#print axioms certified1866
def sourceMap1866swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1866swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1866swap_checked : acceptsGraphIso
    (source (graph core1866) (root 10) 2 0) DegreeTwoThreeSpectrum3446.graph sourceMap1866swap=true := by decide +kernel
theorem fusedMap1866swap_checked : acceptsGraphIso
    (fused (graph core1866) (root 10) 2 0) DegreeTwoThreeSpectrum3456.graph fusedMap1866swap=true := by decide +kernel
theorem certified1866swap : Certified (graph core1866) (root 10) 2 0 :=
  of_native_maps core1866 DegreeTwoThreeSpectrum3446.graph DegreeTwoThreeSpectrum3456.graph
    sourceMap1866swap fusedMap1866swap sourceMap1866swap_checked fusedMap1866swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1866
#print axioms sourceMap1866swap_checked
#print axioms fusedMap1866swap_checked
#print axioms certified1866swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
