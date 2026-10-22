/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2180 : Family 8 := level8.get ⟨183,by decide⟩
def sourceMap2180 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2180 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2180_checked : acceptsGraphIso
    (source (graph core2180) (root 8) 0 4) DegreeTwoThreeSpectrum2962.graph sourceMap2180=true := by decide +kernel
theorem fusedMap2180_checked : acceptsGraphIso
    (fused (graph core2180) (root 8) 0 4) DegreeTwoThreeSpectrum2964.graph fusedMap2180=true := by decide +kernel
theorem certified2180 : Certified (graph core2180) (root 8) 0 4 :=
  of_native_maps core2180 DegreeTwoThreeSpectrum2962.graph DegreeTwoThreeSpectrum2964.graph
    sourceMap2180 fusedMap2180 sourceMap2180_checked fusedMap2180_checked
    DegreeTwoThreeFiniteComparisons.comparison2180
#print axioms sourceMap2180_checked
#print axioms fusedMap2180_checked
#print axioms certified2180
def sourceMap2180swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2180swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2180swap_checked : acceptsGraphIso
    (source (graph core2180) (root 8) 4 0) DegreeTwoThreeSpectrum2962.graph sourceMap2180swap=true := by decide +kernel
theorem fusedMap2180swap_checked : acceptsGraphIso
    (fused (graph core2180) (root 8) 4 0) DegreeTwoThreeSpectrum2964.graph fusedMap2180swap=true := by decide +kernel
theorem certified2180swap : Certified (graph core2180) (root 8) 4 0 :=
  of_native_maps core2180 DegreeTwoThreeSpectrum2962.graph DegreeTwoThreeSpectrum2964.graph
    sourceMap2180swap fusedMap2180swap sourceMap2180swap_checked fusedMap2180swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2180
#print axioms sourceMap2180swap_checked
#print axioms fusedMap2180swap_checked
#print axioms certified2180swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
