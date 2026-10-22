/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2931 : Family 10 := level10.get ⟨1388,by decide⟩
def sourceMap2931 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2931 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2931_checked : acceptsGraphIso
    (source (graph core2931) (root 10) 0 4) DegreeTwoThreeSpectrum6749.graph sourceMap2931=true := by decide +kernel
theorem fusedMap2931_checked : acceptsGraphIso
    (fused (graph core2931) (root 10) 0 4) DegreeTwoThreeSpectrum6750.graph fusedMap2931=true := by decide +kernel
theorem certified2931 : Certified (graph core2931) (root 10) 0 4 :=
  of_native_maps core2931 DegreeTwoThreeSpectrum6749.graph DegreeTwoThreeSpectrum6750.graph
    sourceMap2931 fusedMap2931 sourceMap2931_checked fusedMap2931_checked
    DegreeTwoThreeFiniteComparisons.comparison2931
#print axioms sourceMap2931_checked
#print axioms fusedMap2931_checked
#print axioms certified2931
def sourceMap2931swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2931swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2931swap_checked : acceptsGraphIso
    (source (graph core2931) (root 10) 4 0) DegreeTwoThreeSpectrum6749.graph sourceMap2931swap=true := by decide +kernel
theorem fusedMap2931swap_checked : acceptsGraphIso
    (fused (graph core2931) (root 10) 4 0) DegreeTwoThreeSpectrum6750.graph fusedMap2931swap=true := by decide +kernel
theorem certified2931swap : Certified (graph core2931) (root 10) 4 0 :=
  of_native_maps core2931 DegreeTwoThreeSpectrum6749.graph DegreeTwoThreeSpectrum6750.graph
    sourceMap2931swap fusedMap2931swap sourceMap2931swap_checked fusedMap2931swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2931
#print axioms sourceMap2931swap_checked
#print axioms fusedMap2931swap_checked
#print axioms certified2931swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
