/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2360 : Family 9 := level9.get ⟨451,by decide⟩
def sourceMap2360 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2360 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2360_checked : acceptsGraphIso
    (source (graph core2360) (root 9) 0 4) DegreeTwoThreeSpectrum4466.graph sourceMap2360=true := by decide +kernel
theorem fusedMap2360_checked : acceptsGraphIso
    (fused (graph core2360) (root 9) 0 4) DegreeTwoThreeSpectrum4467.graph fusedMap2360=true := by decide +kernel
theorem certified2360 : Certified (graph core2360) (root 9) 0 4 :=
  of_native_maps core2360 DegreeTwoThreeSpectrum4466.graph DegreeTwoThreeSpectrum4467.graph
    sourceMap2360 fusedMap2360 sourceMap2360_checked fusedMap2360_checked
    DegreeTwoThreeFiniteComparisons.comparison2360
#print axioms sourceMap2360_checked
#print axioms fusedMap2360_checked
#print axioms certified2360
def sourceMap2360swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2360swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2360swap_checked : acceptsGraphIso
    (source (graph core2360) (root 9) 4 0) DegreeTwoThreeSpectrum4466.graph sourceMap2360swap=true := by decide +kernel
theorem fusedMap2360swap_checked : acceptsGraphIso
    (fused (graph core2360) (root 9) 4 0) DegreeTwoThreeSpectrum4467.graph fusedMap2360swap=true := by decide +kernel
theorem certified2360swap : Certified (graph core2360) (root 9) 4 0 :=
  of_native_maps core2360 DegreeTwoThreeSpectrum4466.graph DegreeTwoThreeSpectrum4467.graph
    sourceMap2360swap fusedMap2360swap sourceMap2360swap_checked fusedMap2360swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2360
#print axioms sourceMap2360swap_checked
#print axioms fusedMap2360swap_checked
#print axioms certified2360swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
