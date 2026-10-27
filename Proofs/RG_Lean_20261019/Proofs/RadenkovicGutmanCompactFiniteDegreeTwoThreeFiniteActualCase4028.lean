/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4028 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap4028 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,9,7,8,2,1,0,10,11,12,13,14,15] (sourceLabel 4 1 8 v)
def fusedMap4028 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 1 8 v)
theorem sourceMap4028_checked : acceptsGraphIso
    (source (graph core4028) (root 4) 1 8) DegreeTwoThreeSpectrum3918.graph sourceMap4028=true := by decide +kernel
theorem fusedMap4028_checked : acceptsGraphIso
    (fused (graph core4028) (root 4) 1 8) DegreeTwoThreeSpectrum3855.graph fusedMap4028=true := by decide +kernel
theorem certified4028 : Certified (graph core4028) (root 4) 1 8 :=
  of_native_maps core4028 DegreeTwoThreeSpectrum3918.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap4028 fusedMap4028 sourceMap4028_checked fusedMap4028_checked
    DegreeTwoThreeFiniteComparisons.comparison4028
#print axioms sourceMap4028_checked
#print axioms fusedMap4028_checked
#print axioms certified4028
def sourceMap4028swap : (Vertices 4 ⊕ Fin 9 ⊕ Fin 2) → Fin 16 :=
  fun v => ![3,4,5,6,9,2,1,0,10,11,12,13,14,15,7,8] (sourceLabel 4 8 1 v)
def fusedMap4028swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 8 1 v)
theorem sourceMap4028swap_checked : acceptsGraphIso
    (source (graph core4028) (root 4) 8 1) DegreeTwoThreeSpectrum3918.graph sourceMap4028swap=true := by decide +kernel
theorem fusedMap4028swap_checked : acceptsGraphIso
    (fused (graph core4028) (root 4) 8 1) DegreeTwoThreeSpectrum3855.graph fusedMap4028swap=true := by decide +kernel
theorem certified4028swap : Certified (graph core4028) (root 4) 8 1 :=
  of_native_maps core4028 DegreeTwoThreeSpectrum3918.graph DegreeTwoThreeSpectrum3855.graph
    sourceMap4028swap fusedMap4028swap sourceMap4028swap_checked fusedMap4028swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4028
#print axioms sourceMap4028swap_checked
#print axioms fusedMap4028swap_checked
#print axioms certified4028swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
