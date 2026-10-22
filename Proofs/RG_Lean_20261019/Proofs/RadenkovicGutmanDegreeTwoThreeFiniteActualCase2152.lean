/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2152 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap2152 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2152 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2152_checked : acceptsGraphIso
    (source (graph core2152) (root 8) 0 4) DegreeTwoThreeSpectrum2545.graph sourceMap2152=true := by decide +kernel
theorem fusedMap2152_checked : acceptsGraphIso
    (fused (graph core2152) (root 8) 0 4) DegreeTwoThreeSpectrum2547.graph fusedMap2152=true := by decide +kernel
theorem certified2152 : Certified (graph core2152) (root 8) 0 4 :=
  of_native_maps core2152 DegreeTwoThreeSpectrum2545.graph DegreeTwoThreeSpectrum2547.graph
    sourceMap2152 fusedMap2152 sourceMap2152_checked fusedMap2152_checked
    DegreeTwoThreeFiniteComparisons.comparison2152
#print axioms sourceMap2152_checked
#print axioms fusedMap2152_checked
#print axioms certified2152
def sourceMap2152swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2152swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2152swap_checked : acceptsGraphIso
    (source (graph core2152) (root 8) 4 0) DegreeTwoThreeSpectrum2545.graph sourceMap2152swap=true := by decide +kernel
theorem fusedMap2152swap_checked : acceptsGraphIso
    (fused (graph core2152) (root 8) 4 0) DegreeTwoThreeSpectrum2547.graph fusedMap2152swap=true := by decide +kernel
theorem certified2152swap : Certified (graph core2152) (root 8) 4 0 :=
  of_native_maps core2152 DegreeTwoThreeSpectrum2545.graph DegreeTwoThreeSpectrum2547.graph
    sourceMap2152swap fusedMap2152swap sourceMap2152swap_checked fusedMap2152swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2152
#print axioms sourceMap2152swap_checked
#print axioms fusedMap2152swap_checked
#print axioms certified2152swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
