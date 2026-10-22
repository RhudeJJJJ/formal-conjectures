/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2157 : Family 8 := level8.get ⟨129,by decide⟩
def sourceMap2157 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2157 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2157_checked : acceptsGraphIso
    (source (graph core2157) (root 8) 0 4) DegreeTwoThreeSpectrum2606.graph sourceMap2157=true := by decide +kernel
theorem fusedMap2157_checked : acceptsGraphIso
    (fused (graph core2157) (root 8) 0 4) DegreeTwoThreeSpectrum2608.graph fusedMap2157=true := by decide +kernel
theorem certified2157 : Certified (graph core2157) (root 8) 0 4 :=
  of_native_maps core2157 DegreeTwoThreeSpectrum2606.graph DegreeTwoThreeSpectrum2608.graph
    sourceMap2157 fusedMap2157 sourceMap2157_checked fusedMap2157_checked
    DegreeTwoThreeFiniteComparisons.comparison2157
#print axioms sourceMap2157_checked
#print axioms fusedMap2157_checked
#print axioms certified2157
def sourceMap2157swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2157swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2157swap_checked : acceptsGraphIso
    (source (graph core2157) (root 8) 4 0) DegreeTwoThreeSpectrum2606.graph sourceMap2157swap=true := by decide +kernel
theorem fusedMap2157swap_checked : acceptsGraphIso
    (fused (graph core2157) (root 8) 4 0) DegreeTwoThreeSpectrum2608.graph fusedMap2157swap=true := by decide +kernel
theorem certified2157swap : Certified (graph core2157) (root 8) 4 0 :=
  of_native_maps core2157 DegreeTwoThreeSpectrum2606.graph DegreeTwoThreeSpectrum2608.graph
    sourceMap2157swap fusedMap2157swap sourceMap2157swap_checked fusedMap2157swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2157
#print axioms sourceMap2157swap_checked
#print axioms fusedMap2157swap_checked
#print axioms certified2157swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
