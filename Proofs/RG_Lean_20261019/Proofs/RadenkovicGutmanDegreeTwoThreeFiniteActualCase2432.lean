/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2432 : Family 9 := level9.get ⟨618,by decide⟩
def sourceMap2432 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2432 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2432_checked : acceptsGraphIso
    (source (graph core2432) (root 9) 0 4) DegreeTwoThreeSpectrum4760.graph sourceMap2432=true := by decide +kernel
theorem fusedMap2432_checked : acceptsGraphIso
    (fused (graph core2432) (root 9) 0 4) DegreeTwoThreeSpectrum4332.graph fusedMap2432=true := by decide +kernel
theorem certified2432 : Certified (graph core2432) (root 9) 0 4 :=
  of_native_maps core2432 DegreeTwoThreeSpectrum4760.graph DegreeTwoThreeSpectrum4332.graph
    sourceMap2432 fusedMap2432 sourceMap2432_checked fusedMap2432_checked
    DegreeTwoThreeFiniteComparisons.comparison2432
#print axioms sourceMap2432_checked
#print axioms fusedMap2432_checked
#print axioms certified2432
def sourceMap2432swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2432swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2432swap_checked : acceptsGraphIso
    (source (graph core2432) (root 9) 4 0) DegreeTwoThreeSpectrum4760.graph sourceMap2432swap=true := by decide +kernel
theorem fusedMap2432swap_checked : acceptsGraphIso
    (fused (graph core2432) (root 9) 4 0) DegreeTwoThreeSpectrum4332.graph fusedMap2432swap=true := by decide +kernel
theorem certified2432swap : Certified (graph core2432) (root 9) 4 0 :=
  of_native_maps core2432 DegreeTwoThreeSpectrum4760.graph DegreeTwoThreeSpectrum4332.graph
    sourceMap2432swap fusedMap2432swap sourceMap2432swap_checked fusedMap2432swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2432
#print axioms sourceMap2432swap_checked
#print axioms fusedMap2432swap_checked
#print axioms certified2432swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
