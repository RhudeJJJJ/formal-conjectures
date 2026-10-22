/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2611 : Family 10 := level10.get ⟨567,by decide⟩
def sourceMap2611 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2611 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2611_checked : acceptsGraphIso
    (source (graph core2611) (root 10) 0 4) DegreeTwoThreeSpectrum6212.graph sourceMap2611=true := by decide +kernel
theorem fusedMap2611_checked : acceptsGraphIso
    (fused (graph core2611) (root 10) 0 4) DegreeTwoThreeSpectrum5231.graph fusedMap2611=true := by decide +kernel
theorem certified2611 : Certified (graph core2611) (root 10) 0 4 :=
  of_native_maps core2611 DegreeTwoThreeSpectrum6212.graph DegreeTwoThreeSpectrum5231.graph
    sourceMap2611 fusedMap2611 sourceMap2611_checked fusedMap2611_checked
    DegreeTwoThreeFiniteComparisons.comparison2611
#print axioms sourceMap2611_checked
#print axioms fusedMap2611_checked
#print axioms certified2611
def sourceMap2611swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2611swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2611swap_checked : acceptsGraphIso
    (source (graph core2611) (root 10) 4 0) DegreeTwoThreeSpectrum6212.graph sourceMap2611swap=true := by decide +kernel
theorem fusedMap2611swap_checked : acceptsGraphIso
    (fused (graph core2611) (root 10) 4 0) DegreeTwoThreeSpectrum5231.graph fusedMap2611swap=true := by decide +kernel
theorem certified2611swap : Certified (graph core2611) (root 10) 4 0 :=
  of_native_maps core2611 DegreeTwoThreeSpectrum6212.graph DegreeTwoThreeSpectrum5231.graph
    sourceMap2611swap fusedMap2611swap sourceMap2611swap_checked fusedMap2611swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2611
#print axioms sourceMap2611swap_checked
#print axioms fusedMap2611swap_checked
#print axioms certified2611swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
