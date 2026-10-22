/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2813 : Family 10 := level10.get ⟨1111,by decide⟩
def sourceMap2813 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2813 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2813_checked : acceptsGraphIso
    (source (graph core2813) (root 10) 0 4) DegreeTwoThreeSpectrum6207.graph sourceMap2813=true := by decide +kernel
theorem fusedMap2813_checked : acceptsGraphIso
    (fused (graph core2813) (root 10) 0 4) DegreeTwoThreeSpectrum6208.graph fusedMap2813=true := by decide +kernel
theorem certified2813 : Certified (graph core2813) (root 10) 0 4 :=
  of_native_maps core2813 DegreeTwoThreeSpectrum6207.graph DegreeTwoThreeSpectrum6208.graph
    sourceMap2813 fusedMap2813 sourceMap2813_checked fusedMap2813_checked
    DegreeTwoThreeFiniteComparisons.comparison2813
#print axioms sourceMap2813_checked
#print axioms fusedMap2813_checked
#print axioms certified2813
def sourceMap2813swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2813swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2813swap_checked : acceptsGraphIso
    (source (graph core2813) (root 10) 4 0) DegreeTwoThreeSpectrum6207.graph sourceMap2813swap=true := by decide +kernel
theorem fusedMap2813swap_checked : acceptsGraphIso
    (fused (graph core2813) (root 10) 4 0) DegreeTwoThreeSpectrum6208.graph fusedMap2813swap=true := by decide +kernel
theorem certified2813swap : Certified (graph core2813) (root 10) 4 0 :=
  of_native_maps core2813 DegreeTwoThreeSpectrum6207.graph DegreeTwoThreeSpectrum6208.graph
    sourceMap2813swap fusedMap2813swap sourceMap2813swap_checked fusedMap2813swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2813
#print axioms sourceMap2813swap_checked
#print axioms fusedMap2813swap_checked
#print axioms certified2813swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
