/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2058 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap2058 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap2058 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap2058_checked : acceptsGraphIso
    (source (graph core2058) (root 4) 0 4) DegreeOneSmallSpectrum177.graph sourceMap2058=true := by decide +kernel
theorem fusedMap2058_checked : acceptsGraphIso
    (fused (graph core2058) (root 4) 0 4) DegreeOneSmallSpectrum182.graph fusedMap2058=true := by decide +kernel
theorem certified2058 : Certified (graph core2058) (root 4) 0 4 :=
  of_native_maps core2058 DegreeOneSmallSpectrum177.graph DegreeOneSmallSpectrum182.graph
    sourceMap2058 fusedMap2058 sourceMap2058_checked fusedMap2058_checked
    DegreeTwoThreeFiniteComparisons.comparison2058
#print axioms sourceMap2058_checked
#print axioms fusedMap2058_checked
#print axioms certified2058
def sourceMap2058swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap2058swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap2058swap_checked : acceptsGraphIso
    (source (graph core2058) (root 4) 4 0) DegreeOneSmallSpectrum177.graph sourceMap2058swap=true := by decide +kernel
theorem fusedMap2058swap_checked : acceptsGraphIso
    (fused (graph core2058) (root 4) 4 0) DegreeOneSmallSpectrum182.graph fusedMap2058swap=true := by decide +kernel
theorem certified2058swap : Certified (graph core2058) (root 4) 4 0 :=
  of_native_maps core2058 DegreeOneSmallSpectrum177.graph DegreeOneSmallSpectrum182.graph
    sourceMap2058swap fusedMap2058swap sourceMap2058swap_checked fusedMap2058swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2058
#print axioms sourceMap2058swap_checked
#print axioms fusedMap2058swap_checked
#print axioms certified2058swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
