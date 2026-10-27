/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4030 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap4030 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,7,8,5,6,3,2,1,0,9,10,11,12,13,14] (sourceLabel 2 1 9 v)
def fusedMap4030 : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 1 9 v)
theorem sourceMap4030_checked : acceptsGraphIso
    (source (graph core4030) (root 2) 1 9) DegreeTwoThreeSpectrum2359.graph sourceMap4030=true := by decide +kernel
theorem fusedMap4030_checked : acceptsGraphIso
    (fused (graph core4030) (root 2) 1 9) DegreeTwoThreeSpectrum2309.graph fusedMap4030=true := by decide +kernel
theorem certified4030 : Certified (graph core4030) (root 2) 1 9 :=
  of_native_maps core4030 DegreeTwoThreeSpectrum2359.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap4030 fusedMap4030 sourceMap4030_checked fusedMap4030_checked
    DegreeTwoThreeFiniteComparisons.comparison4030
#print axioms sourceMap4030_checked
#print axioms fusedMap4030_checked
#print axioms certified4030
def sourceMap4030swap : (Vertices 2 ⊕ Fin 10 ⊕ Fin 2) → Fin 15 :=
  fun v => ![4,7,8,3,2,1,0,9,10,11,12,13,14,5,6] (sourceLabel 2 9 1 v)
def fusedMap4030swap : (Vertices 2 ⊕ Fin 12) → Fin 15 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 2 9 1 v)
theorem sourceMap4030swap_checked : acceptsGraphIso
    (source (graph core4030) (root 2) 9 1) DegreeTwoThreeSpectrum2359.graph sourceMap4030swap=true := by decide +kernel
theorem fusedMap4030swap_checked : acceptsGraphIso
    (fused (graph core4030) (root 2) 9 1) DegreeTwoThreeSpectrum2309.graph fusedMap4030swap=true := by decide +kernel
theorem certified4030swap : Certified (graph core4030) (root 2) 9 1 :=
  of_native_maps core4030 DegreeTwoThreeSpectrum2359.graph DegreeTwoThreeSpectrum2309.graph
    sourceMap4030swap fusedMap4030swap sourceMap4030swap_checked fusedMap4030swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4030
#print axioms sourceMap4030swap_checked
#print axioms fusedMap4030swap_checked
#print axioms certified4030swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
