/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2071 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap2071 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2071 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2071_checked : acceptsGraphIso
    (source (graph core2071) (root 6) 0 4) DegreeOneSmallSpectrum1049.graph sourceMap2071=true := by decide +kernel
theorem fusedMap2071_checked : acceptsGraphIso
    (fused (graph core2071) (root 6) 0 4) DegreeOneSmallSpectrum864.graph fusedMap2071=true := by decide +kernel
theorem certified2071 : Certified (graph core2071) (root 6) 0 4 :=
  of_native_maps core2071 DegreeOneSmallSpectrum1049.graph DegreeOneSmallSpectrum864.graph
    sourceMap2071 fusedMap2071 sourceMap2071_checked fusedMap2071_checked
    DegreeTwoThreeFiniteComparisons.comparison2071
#print axioms sourceMap2071_checked
#print axioms fusedMap2071_checked
#print axioms certified2071
def sourceMap2071swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2071swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2071swap_checked : acceptsGraphIso
    (source (graph core2071) (root 6) 4 0) DegreeOneSmallSpectrum1049.graph sourceMap2071swap=true := by decide +kernel
theorem fusedMap2071swap_checked : acceptsGraphIso
    (fused (graph core2071) (root 6) 4 0) DegreeOneSmallSpectrum864.graph fusedMap2071swap=true := by decide +kernel
theorem certified2071swap : Certified (graph core2071) (root 6) 4 0 :=
  of_native_maps core2071 DegreeOneSmallSpectrum1049.graph DegreeOneSmallSpectrum864.graph
    sourceMap2071swap fusedMap2071swap sourceMap2071swap_checked fusedMap2071swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2071
#print axioms sourceMap2071swap_checked
#print axioms fusedMap2071swap_checked
#print axioms certified2071swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
