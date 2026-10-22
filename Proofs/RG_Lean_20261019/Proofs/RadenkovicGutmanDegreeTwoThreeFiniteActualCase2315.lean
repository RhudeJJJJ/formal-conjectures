/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2315 : Family 9 := level9.get ⟨336,by decide⟩
def sourceMap2315 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2315 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2315_checked : acceptsGraphIso
    (source (graph core2315) (root 9) 0 4) DegreeTwoThreeSpectrum4220.graph sourceMap2315=true := by decide +kernel
theorem fusedMap2315_checked : acceptsGraphIso
    (fused (graph core2315) (root 9) 0 4) DegreeTwoThreeSpectrum4221.graph fusedMap2315=true := by decide +kernel
theorem certified2315 : Certified (graph core2315) (root 9) 0 4 :=
  of_native_maps core2315 DegreeTwoThreeSpectrum4220.graph DegreeTwoThreeSpectrum4221.graph
    sourceMap2315 fusedMap2315 sourceMap2315_checked fusedMap2315_checked
    DegreeTwoThreeFiniteComparisons.comparison2315
#print axioms sourceMap2315_checked
#print axioms fusedMap2315_checked
#print axioms certified2315
def sourceMap2315swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2315swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2315swap_checked : acceptsGraphIso
    (source (graph core2315) (root 9) 4 0) DegreeTwoThreeSpectrum4220.graph sourceMap2315swap=true := by decide +kernel
theorem fusedMap2315swap_checked : acceptsGraphIso
    (fused (graph core2315) (root 9) 4 0) DegreeTwoThreeSpectrum4221.graph fusedMap2315swap=true := by decide +kernel
theorem certified2315swap : Certified (graph core2315) (root 9) 4 0 :=
  of_native_maps core2315 DegreeTwoThreeSpectrum4220.graph DegreeTwoThreeSpectrum4221.graph
    sourceMap2315swap fusedMap2315swap sourceMap2315swap_checked fusedMap2315swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2315
#print axioms sourceMap2315swap_checked
#print axioms fusedMap2315swap_checked
#print axioms certified2315swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
