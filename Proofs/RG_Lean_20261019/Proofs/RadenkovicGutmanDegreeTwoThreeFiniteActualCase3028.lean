/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3028 : Family 10 := level10.get ⟨1634,by decide⟩
def sourceMap3028 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3028 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3028_checked : acceptsGraphIso
    (source (graph core3028) (root 10) 0 4) DegreeTwoThreeSpectrum7189.graph sourceMap3028=true := by decide +kernel
theorem fusedMap3028_checked : acceptsGraphIso
    (fused (graph core3028) (root 10) 0 4) DegreeTwoThreeSpectrum6202.graph fusedMap3028=true := by decide +kernel
theorem certified3028 : Certified (graph core3028) (root 10) 0 4 :=
  of_native_maps core3028 DegreeTwoThreeSpectrum7189.graph DegreeTwoThreeSpectrum6202.graph
    sourceMap3028 fusedMap3028 sourceMap3028_checked fusedMap3028_checked
    DegreeTwoThreeFiniteComparisons.comparison3028
#print axioms sourceMap3028_checked
#print axioms fusedMap3028_checked
#print axioms certified3028
def sourceMap3028swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3028swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3028swap_checked : acceptsGraphIso
    (source (graph core3028) (root 10) 4 0) DegreeTwoThreeSpectrum7189.graph sourceMap3028swap=true := by decide +kernel
theorem fusedMap3028swap_checked : acceptsGraphIso
    (fused (graph core3028) (root 10) 4 0) DegreeTwoThreeSpectrum6202.graph fusedMap3028swap=true := by decide +kernel
theorem certified3028swap : Certified (graph core3028) (root 10) 4 0 :=
  of_native_maps core3028 DegreeTwoThreeSpectrum7189.graph DegreeTwoThreeSpectrum6202.graph
    sourceMap3028swap fusedMap3028swap sourceMap3028swap_checked fusedMap3028swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3028
#print axioms sourceMap3028swap_checked
#print axioms fusedMap3028swap_checked
#print axioms certified3028swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
