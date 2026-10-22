/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2906 : Family 10 := level10.get ⟨1333,by decide⟩
def sourceMap2906 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2906 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2906_checked : acceptsGraphIso
    (source (graph core2906) (root 10) 0 4) DegreeTwoThreeSpectrum6647.graph sourceMap2906=true := by decide +kernel
theorem fusedMap2906_checked : acceptsGraphIso
    (fused (graph core2906) (root 10) 0 4) DegreeTwoThreeSpectrum6648.graph fusedMap2906=true := by decide +kernel
theorem certified2906 : Certified (graph core2906) (root 10) 0 4 :=
  of_native_maps core2906 DegreeTwoThreeSpectrum6647.graph DegreeTwoThreeSpectrum6648.graph
    sourceMap2906 fusedMap2906 sourceMap2906_checked fusedMap2906_checked
    DegreeTwoThreeFiniteComparisons.comparison2906
#print axioms sourceMap2906_checked
#print axioms fusedMap2906_checked
#print axioms certified2906
def sourceMap2906swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2906swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2906swap_checked : acceptsGraphIso
    (source (graph core2906) (root 10) 4 0) DegreeTwoThreeSpectrum6647.graph sourceMap2906swap=true := by decide +kernel
theorem fusedMap2906swap_checked : acceptsGraphIso
    (fused (graph core2906) (root 10) 4 0) DegreeTwoThreeSpectrum6648.graph fusedMap2906swap=true := by decide +kernel
theorem certified2906swap : Certified (graph core2906) (root 10) 4 0 :=
  of_native_maps core2906 DegreeTwoThreeSpectrum6647.graph DegreeTwoThreeSpectrum6648.graph
    sourceMap2906swap fusedMap2906swap sourceMap2906swap_checked fusedMap2906swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2906
#print axioms sourceMap2906swap_checked
#print axioms fusedMap2906swap_checked
#print axioms certified2906swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
