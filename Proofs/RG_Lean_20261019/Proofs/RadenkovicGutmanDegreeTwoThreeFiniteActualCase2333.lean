/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2333 : Family 9 := level9.get ⟨382,by decide⟩
def sourceMap2333 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2333 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2333_checked : acceptsGraphIso
    (source (graph core2333) (root 9) 0 4) DegreeTwoThreeSpectrum4320.graph sourceMap2333=true := by decide +kernel
theorem fusedMap2333_checked : acceptsGraphIso
    (fused (graph core2333) (root 9) 0 4) DegreeTwoThreeSpectrum4321.graph fusedMap2333=true := by decide +kernel
theorem certified2333 : Certified (graph core2333) (root 9) 0 4 :=
  of_native_maps core2333 DegreeTwoThreeSpectrum4320.graph DegreeTwoThreeSpectrum4321.graph
    sourceMap2333 fusedMap2333 sourceMap2333_checked fusedMap2333_checked
    DegreeTwoThreeFiniteComparisons.comparison2333
#print axioms sourceMap2333_checked
#print axioms fusedMap2333_checked
#print axioms certified2333
def sourceMap2333swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2333swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2333swap_checked : acceptsGraphIso
    (source (graph core2333) (root 9) 4 0) DegreeTwoThreeSpectrum4320.graph sourceMap2333swap=true := by decide +kernel
theorem fusedMap2333swap_checked : acceptsGraphIso
    (fused (graph core2333) (root 9) 4 0) DegreeTwoThreeSpectrum4321.graph fusedMap2333swap=true := by decide +kernel
theorem certified2333swap : Certified (graph core2333) (root 9) 4 0 :=
  of_native_maps core2333 DegreeTwoThreeSpectrum4320.graph DegreeTwoThreeSpectrum4321.graph
    sourceMap2333swap fusedMap2333swap sourceMap2333swap_checked fusedMap2333swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2333
#print axioms sourceMap2333swap_checked
#print axioms fusedMap2333swap_checked
#print axioms certified2333swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
