/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2006 : Family 10 := level10.get ⟨1635,by decide⟩
def sourceMap2006 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2006 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2006_checked : acceptsGraphIso
    (source (graph core2006) (root 10) 0 2) DegreeTwoThreeSpectrum3793.graph sourceMap2006=true := by decide +kernel
theorem fusedMap2006_checked : acceptsGraphIso
    (fused (graph core2006) (root 10) 0 2) DegreeTwoThreeSpectrum3180.graph fusedMap2006=true := by decide +kernel
theorem certified2006 : Certified (graph core2006) (root 10) 0 2 :=
  of_native_maps core2006 DegreeTwoThreeSpectrum3793.graph DegreeTwoThreeSpectrum3180.graph
    sourceMap2006 fusedMap2006 sourceMap2006_checked fusedMap2006_checked
    DegreeTwoThreeFiniteComparisons.comparison2006
#print axioms sourceMap2006_checked
#print axioms fusedMap2006_checked
#print axioms certified2006
def sourceMap2006swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2006swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2006swap_checked : acceptsGraphIso
    (source (graph core2006) (root 10) 2 0) DegreeTwoThreeSpectrum3793.graph sourceMap2006swap=true := by decide +kernel
theorem fusedMap2006swap_checked : acceptsGraphIso
    (fused (graph core2006) (root 10) 2 0) DegreeTwoThreeSpectrum3180.graph fusedMap2006swap=true := by decide +kernel
theorem certified2006swap : Certified (graph core2006) (root 10) 2 0 :=
  of_native_maps core2006 DegreeTwoThreeSpectrum3793.graph DegreeTwoThreeSpectrum3180.graph
    sourceMap2006swap fusedMap2006swap sourceMap2006swap_checked fusedMap2006swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2006
#print axioms sourceMap2006swap_checked
#print axioms fusedMap2006swap_checked
#print axioms certified2006swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
