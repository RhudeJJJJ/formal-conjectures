/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2148 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap2148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2148 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2148_checked : acceptsGraphIso
    (source (graph core2148) (root 8) 0 4) DegreeTwoThreeSpectrum2486.graph sourceMap2148=true := by decide +kernel
theorem fusedMap2148_checked : acceptsGraphIso
    (fused (graph core2148) (root 8) 0 4) DegreeTwoThreeSpectrum2488.graph fusedMap2148=true := by decide +kernel
theorem certified2148 : Certified (graph core2148) (root 8) 0 4 :=
  of_native_maps core2148 DegreeTwoThreeSpectrum2486.graph DegreeTwoThreeSpectrum2488.graph
    sourceMap2148 fusedMap2148 sourceMap2148_checked fusedMap2148_checked
    DegreeTwoThreeFiniteComparisons.comparison2148
#print axioms sourceMap2148_checked
#print axioms fusedMap2148_checked
#print axioms certified2148
def sourceMap2148swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2148swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2148swap_checked : acceptsGraphIso
    (source (graph core2148) (root 8) 4 0) DegreeTwoThreeSpectrum2486.graph sourceMap2148swap=true := by decide +kernel
theorem fusedMap2148swap_checked : acceptsGraphIso
    (fused (graph core2148) (root 8) 4 0) DegreeTwoThreeSpectrum2488.graph fusedMap2148swap=true := by decide +kernel
theorem certified2148swap : Certified (graph core2148) (root 8) 4 0 :=
  of_native_maps core2148 DegreeTwoThreeSpectrum2486.graph DegreeTwoThreeSpectrum2488.graph
    sourceMap2148swap fusedMap2148swap sourceMap2148swap_checked fusedMap2148swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2148
#print axioms sourceMap2148swap_checked
#print axioms fusedMap2148swap_checked
#print axioms certified2148swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
