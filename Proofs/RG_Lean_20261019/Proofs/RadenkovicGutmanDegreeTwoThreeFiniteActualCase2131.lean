/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2131 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap2131 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2131 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2131_checked : acceptsGraphIso
    (source (graph core2131) (root 8) 0 4) DegreeTwoThreeSpectrum2689.graph sourceMap2131=true := by decide +kernel
theorem fusedMap2131_checked : acceptsGraphIso
    (fused (graph core2131) (root 8) 0 4) DegreeTwoThreeSpectrum2352.graph fusedMap2131=true := by decide +kernel
theorem certified2131 : Certified (graph core2131) (root 8) 0 4 :=
  of_native_maps core2131 DegreeTwoThreeSpectrum2689.graph DegreeTwoThreeSpectrum2352.graph
    sourceMap2131 fusedMap2131 sourceMap2131_checked fusedMap2131_checked
    DegreeTwoThreeFiniteComparisons.comparison2131
#print axioms sourceMap2131_checked
#print axioms fusedMap2131_checked
#print axioms certified2131
def sourceMap2131swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2131swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2131swap_checked : acceptsGraphIso
    (source (graph core2131) (root 8) 4 0) DegreeTwoThreeSpectrum2689.graph sourceMap2131swap=true := by decide +kernel
theorem fusedMap2131swap_checked : acceptsGraphIso
    (fused (graph core2131) (root 8) 4 0) DegreeTwoThreeSpectrum2352.graph fusedMap2131swap=true := by decide +kernel
theorem certified2131swap : Certified (graph core2131) (root 8) 4 0 :=
  of_native_maps core2131 DegreeTwoThreeSpectrum2689.graph DegreeTwoThreeSpectrum2352.graph
    sourceMap2131swap fusedMap2131swap sourceMap2131swap_checked fusedMap2131swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2131
#print axioms sourceMap2131swap_checked
#print axioms fusedMap2131swap_checked
#print axioms certified2131swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
