/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2028 : Family 10 := level10.get ⟨1706,by decide⟩
def sourceMap2028 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2028 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2028_checked : acceptsGraphIso
    (source (graph core2028) (root 10) 0 2) DegreeTwoThreeSpectrum3822.graph sourceMap2028=true := by decide +kernel
theorem fusedMap2028_checked : acceptsGraphIso
    (fused (graph core2028) (root 10) 0 2) DegreeTwoThreeSpectrum3382.graph fusedMap2028=true := by decide +kernel
theorem certified2028 : Certified (graph core2028) (root 10) 0 2 :=
  of_native_maps core2028 DegreeTwoThreeSpectrum3822.graph DegreeTwoThreeSpectrum3382.graph
    sourceMap2028 fusedMap2028 sourceMap2028_checked fusedMap2028_checked
    DegreeTwoThreeFiniteComparisons.comparison2028
#print axioms sourceMap2028_checked
#print axioms fusedMap2028_checked
#print axioms certified2028
def sourceMap2028swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2028swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2028swap_checked : acceptsGraphIso
    (source (graph core2028) (root 10) 2 0) DegreeTwoThreeSpectrum3822.graph sourceMap2028swap=true := by decide +kernel
theorem fusedMap2028swap_checked : acceptsGraphIso
    (fused (graph core2028) (root 10) 2 0) DegreeTwoThreeSpectrum3382.graph fusedMap2028swap=true := by decide +kernel
theorem certified2028swap : Certified (graph core2028) (root 10) 2 0 :=
  of_native_maps core2028 DegreeTwoThreeSpectrum3822.graph DegreeTwoThreeSpectrum3382.graph
    sourceMap2028swap fusedMap2028swap sourceMap2028swap_checked fusedMap2028swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2028
#print axioms sourceMap2028swap_checked
#print axioms fusedMap2028swap_checked
#print axioms certified2028swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
