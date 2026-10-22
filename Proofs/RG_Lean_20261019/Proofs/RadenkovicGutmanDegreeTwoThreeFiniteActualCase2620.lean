/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2620 : Family 10 := level10.get ⟨597,by decide⟩
def sourceMap2620 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2620 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2620_checked : acceptsGraphIso
    (source (graph core2620) (root 10) 0 4) DegreeTwoThreeSpectrum6306.graph sourceMap2620=true := by decide +kernel
theorem fusedMap2620_checked : acceptsGraphIso
    (fused (graph core2620) (root 10) 0 4) DegreeTwoThreeSpectrum5271.graph fusedMap2620=true := by decide +kernel
theorem certified2620 : Certified (graph core2620) (root 10) 0 4 :=
  of_native_maps core2620 DegreeTwoThreeSpectrum6306.graph DegreeTwoThreeSpectrum5271.graph
    sourceMap2620 fusedMap2620 sourceMap2620_checked fusedMap2620_checked
    DegreeTwoThreeFiniteComparisons.comparison2620
#print axioms sourceMap2620_checked
#print axioms fusedMap2620_checked
#print axioms certified2620
def sourceMap2620swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2620swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2620swap_checked : acceptsGraphIso
    (source (graph core2620) (root 10) 4 0) DegreeTwoThreeSpectrum6306.graph sourceMap2620swap=true := by decide +kernel
theorem fusedMap2620swap_checked : acceptsGraphIso
    (fused (graph core2620) (root 10) 4 0) DegreeTwoThreeSpectrum5271.graph fusedMap2620swap=true := by decide +kernel
theorem certified2620swap : Certified (graph core2620) (root 10) 4 0 :=
  of_native_maps core2620 DegreeTwoThreeSpectrum6306.graph DegreeTwoThreeSpectrum5271.graph
    sourceMap2620swap fusedMap2620swap sourceMap2620swap_checked fusedMap2620swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2620
#print axioms sourceMap2620swap_checked
#print axioms fusedMap2620swap_checked
#print axioms certified2620swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
