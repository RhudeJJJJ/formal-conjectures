/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2063 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap2063 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap2063 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap2063_checked : acceptsGraphIso
    (source (graph core2063) (root 5) 0 4) DegreeOneSmallSpectrum571.graph sourceMap2063=true := by decide +kernel
theorem fusedMap2063_checked : acceptsGraphIso
    (fused (graph core2063) (root 5) 0 4) DegreeOneSmallSpectrum387.graph fusedMap2063=true := by decide +kernel
theorem certified2063 : Certified (graph core2063) (root 5) 0 4 :=
  of_native_maps core2063 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum387.graph
    sourceMap2063 fusedMap2063 sourceMap2063_checked fusedMap2063_checked
    DegreeTwoThreeFiniteComparisons.comparison2063
#print axioms sourceMap2063_checked
#print axioms fusedMap2063_checked
#print axioms certified2063
def sourceMap2063swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,7] (sourceLabel 5 4 0 v)
def fusedMap2063swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap2063swap_checked : acceptsGraphIso
    (source (graph core2063) (root 5) 4 0) DegreeOneSmallSpectrum571.graph sourceMap2063swap=true := by decide +kernel
theorem fusedMap2063swap_checked : acceptsGraphIso
    (fused (graph core2063) (root 5) 4 0) DegreeOneSmallSpectrum387.graph fusedMap2063swap=true := by decide +kernel
theorem certified2063swap : Certified (graph core2063) (root 5) 4 0 :=
  of_native_maps core2063 DegreeOneSmallSpectrum571.graph DegreeOneSmallSpectrum387.graph
    sourceMap2063swap fusedMap2063swap sourceMap2063swap_checked fusedMap2063swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2063
#print axioms sourceMap2063swap_checked
#print axioms fusedMap2063swap_checked
#print axioms certified2063swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
