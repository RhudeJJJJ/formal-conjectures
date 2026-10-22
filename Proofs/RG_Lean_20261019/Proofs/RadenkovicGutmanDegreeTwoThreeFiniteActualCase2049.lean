/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2049 : Family 10 := level10.get ⟨1802,by decide⟩
def sourceMap2049 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 0 2 v)
def fusedMap2049 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2049_checked : acceptsGraphIso
    (source (graph core2049) (root 10) 0 2) DegreeTwoThreeSpectrum3733.graph sourceMap2049=true := by decide +kernel
theorem fusedMap2049_checked : acceptsGraphIso
    (fused (graph core2049) (root 10) 0 2) DegreeTwoThreeSpectrum3734.graph fusedMap2049=true := by decide +kernel
theorem certified2049 : Certified (graph core2049) (root 10) 0 2 :=
  of_native_maps core2049 DegreeTwoThreeSpectrum3733.graph DegreeTwoThreeSpectrum3734.graph
    sourceMap2049 fusedMap2049 sourceMap2049_checked fusedMap2049_checked
    DegreeTwoThreeFiniteComparisons.comparison2049
#print axioms sourceMap2049_checked
#print axioms fusedMap2049_checked
#print axioms certified2049
def sourceMap2049swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,11] (sourceLabel 10 2 0 v)
def fusedMap2049swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2049swap_checked : acceptsGraphIso
    (source (graph core2049) (root 10) 2 0) DegreeTwoThreeSpectrum3733.graph sourceMap2049swap=true := by decide +kernel
theorem fusedMap2049swap_checked : acceptsGraphIso
    (fused (graph core2049) (root 10) 2 0) DegreeTwoThreeSpectrum3734.graph fusedMap2049swap=true := by decide +kernel
theorem certified2049swap : Certified (graph core2049) (root 10) 2 0 :=
  of_native_maps core2049 DegreeTwoThreeSpectrum3733.graph DegreeTwoThreeSpectrum3734.graph
    sourceMap2049swap fusedMap2049swap sourceMap2049swap_checked fusedMap2049swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2049
#print axioms sourceMap2049swap_checked
#print axioms fusedMap2049swap_checked
#print axioms certified2049swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
