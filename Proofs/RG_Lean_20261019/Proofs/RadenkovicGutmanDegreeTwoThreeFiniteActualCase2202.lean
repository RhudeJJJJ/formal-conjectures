/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2202 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap2202 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2202 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2202_checked : acceptsGraphIso
    (source (graph core2202) (root 8) 0 4) DegreeTwoThreeSpectrum3422.graph sourceMap2202=true := by decide +kernel
theorem fusedMap2202_checked : acceptsGraphIso
    (fused (graph core2202) (root 8) 0 4) DegreeTwoThreeSpectrum2661.graph fusedMap2202=true := by decide +kernel
theorem certified2202 : Certified (graph core2202) (root 8) 0 4 :=
  of_native_maps core2202 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2661.graph
    sourceMap2202 fusedMap2202 sourceMap2202_checked fusedMap2202_checked
    DegreeTwoThreeFiniteComparisons.comparison2202
#print axioms sourceMap2202_checked
#print axioms fusedMap2202_checked
#print axioms certified2202
def sourceMap2202swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2202swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2202swap_checked : acceptsGraphIso
    (source (graph core2202) (root 8) 4 0) DegreeTwoThreeSpectrum3422.graph sourceMap2202swap=true := by decide +kernel
theorem fusedMap2202swap_checked : acceptsGraphIso
    (fused (graph core2202) (root 8) 4 0) DegreeTwoThreeSpectrum2661.graph fusedMap2202swap=true := by decide +kernel
theorem certified2202swap : Certified (graph core2202) (root 8) 4 0 :=
  of_native_maps core2202 DegreeTwoThreeSpectrum3422.graph DegreeTwoThreeSpectrum2661.graph
    sourceMap2202swap fusedMap2202swap sourceMap2202swap_checked fusedMap2202swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2202
#print axioms sourceMap2202swap_checked
#print axioms fusedMap2202swap_checked
#print axioms certified2202swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
