/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2215 : Family 9 := level9.get ⟨8,by decide⟩
def sourceMap2215 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,8,2,3,4,5,6] (sourceLabel 9 0 4 v)
def fusedMap2215 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (fusedLabel 9 0 4 v)
theorem sourceMap2215_checked : acceptsGraphIso
    (source (graph core2215) (root 9) 0 4) DegreeTwoThreeSpectrum3884.graph sourceMap2215=true := by decide +kernel
theorem fusedMap2215_checked : acceptsGraphIso
    (fused (graph core2215) (root 9) 0 4) DegreeTwoThreeSpectrum3891.graph fusedMap2215=true := by decide +kernel
theorem certified2215 : Certified (graph core2215) (root 9) 0 4 :=
  of_native_maps core2215 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap2215 fusedMap2215 sourceMap2215_checked fusedMap2215_checked
    DegreeTwoThreeFiniteComparisons.comparison2215
#print axioms sourceMap2215_checked
#print axioms fusedMap2215_checked
#print axioms certified2215
def sourceMap2215swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,2,3,4,5,6,8] (sourceLabel 9 4 0 v)
def fusedMap2215swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (fusedLabel 9 4 0 v)
theorem sourceMap2215swap_checked : acceptsGraphIso
    (source (graph core2215) (root 9) 4 0) DegreeTwoThreeSpectrum3884.graph sourceMap2215swap=true := by decide +kernel
theorem fusedMap2215swap_checked : acceptsGraphIso
    (fused (graph core2215) (root 9) 4 0) DegreeTwoThreeSpectrum3891.graph fusedMap2215swap=true := by decide +kernel
theorem certified2215swap : Certified (graph core2215) (root 9) 4 0 :=
  of_native_maps core2215 DegreeTwoThreeSpectrum3884.graph DegreeTwoThreeSpectrum3891.graph
    sourceMap2215swap fusedMap2215swap sourceMap2215swap_checked fusedMap2215swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2215
#print axioms sourceMap2215swap_checked
#print axioms fusedMap2215swap_checked
#print axioms certified2215swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
