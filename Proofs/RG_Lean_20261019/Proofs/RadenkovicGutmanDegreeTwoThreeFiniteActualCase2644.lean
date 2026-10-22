/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2644 : Family 10 := level10.get ⟨664,by decide⟩
def sourceMap2644 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2644 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2644_checked : acceptsGraphIso
    (source (graph core2644) (root 10) 0 4) DegreeTwoThreeSpectrum6445.graph sourceMap2644=true := by decide +kernel
theorem fusedMap2644_checked : acceptsGraphIso
    (fused (graph core2644) (root 10) 0 4) DegreeTwoThreeSpectrum5374.graph fusedMap2644=true := by decide +kernel
theorem certified2644 : Certified (graph core2644) (root 10) 0 4 :=
  of_native_maps core2644 DegreeTwoThreeSpectrum6445.graph DegreeTwoThreeSpectrum5374.graph
    sourceMap2644 fusedMap2644 sourceMap2644_checked fusedMap2644_checked
    DegreeTwoThreeFiniteComparisons.comparison2644
#print axioms sourceMap2644_checked
#print axioms fusedMap2644_checked
#print axioms certified2644
def sourceMap2644swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2644swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2644swap_checked : acceptsGraphIso
    (source (graph core2644) (root 10) 4 0) DegreeTwoThreeSpectrum6445.graph sourceMap2644swap=true := by decide +kernel
theorem fusedMap2644swap_checked : acceptsGraphIso
    (fused (graph core2644) (root 10) 4 0) DegreeTwoThreeSpectrum5374.graph fusedMap2644swap=true := by decide +kernel
theorem certified2644swap : Certified (graph core2644) (root 10) 4 0 :=
  of_native_maps core2644 DegreeTwoThreeSpectrum6445.graph DegreeTwoThreeSpectrum5374.graph
    sourceMap2644swap fusedMap2644swap sourceMap2644swap_checked fusedMap2644swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2644
#print axioms sourceMap2644swap_checked
#print axioms fusedMap2644swap_checked
#print axioms certified2644swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
