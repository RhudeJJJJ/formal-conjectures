/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2792 : Family 10 := level10.get ⟨1058,by decide⟩
def sourceMap2792 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2792 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2792_checked : acceptsGraphIso
    (source (graph core2792) (root 10) 0 4) DegreeTwoThreeSpectrum6100.graph sourceMap2792=true := by decide +kernel
theorem fusedMap2792_checked : acceptsGraphIso
    (fused (graph core2792) (root 10) 0 4) DegreeTwoThreeSpectrum6101.graph fusedMap2792=true := by decide +kernel
theorem certified2792 : Certified (graph core2792) (root 10) 0 4 :=
  of_native_maps core2792 DegreeTwoThreeSpectrum6100.graph DegreeTwoThreeSpectrum6101.graph
    sourceMap2792 fusedMap2792 sourceMap2792_checked fusedMap2792_checked
    DegreeTwoThreeFiniteComparisons.comparison2792
#print axioms sourceMap2792_checked
#print axioms fusedMap2792_checked
#print axioms certified2792
def sourceMap2792swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2792swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2792swap_checked : acceptsGraphIso
    (source (graph core2792) (root 10) 4 0) DegreeTwoThreeSpectrum6100.graph sourceMap2792swap=true := by decide +kernel
theorem fusedMap2792swap_checked : acceptsGraphIso
    (fused (graph core2792) (root 10) 4 0) DegreeTwoThreeSpectrum6101.graph fusedMap2792swap=true := by decide +kernel
theorem certified2792swap : Certified (graph core2792) (root 10) 4 0 :=
  of_native_maps core2792 DegreeTwoThreeSpectrum6100.graph DegreeTwoThreeSpectrum6101.graph
    sourceMap2792swap fusedMap2792swap sourceMap2792swap_checked fusedMap2792swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2792
#print axioms sourceMap2792swap_checked
#print axioms fusedMap2792swap_checked
#print axioms certified2792swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
