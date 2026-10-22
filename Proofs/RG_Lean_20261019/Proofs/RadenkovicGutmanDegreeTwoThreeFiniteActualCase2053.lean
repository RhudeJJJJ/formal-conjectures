/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2053 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap2053 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (sourceLabel 2 0 3 v)
def fusedMap2053 : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![2,3,4,1,0,5,6,7] (fusedLabel 2 0 3 v)
theorem sourceMap2053_checked : acceptsGraphIso
    (source (graph core2053) (root 2) 0 3) DegreeOneSmallSpectrum017.graph sourceMap2053=true := by decide +kernel
theorem fusedMap2053_checked : acceptsGraphIso
    (fused (graph core2053) (root 2) 0 3) DegreeOneSmallSpectrum021.graph fusedMap2053=true := by decide +kernel
theorem certified2053 : Certified (graph core2053) (root 2) 0 3 :=
  of_native_maps core2053 DegreeOneSmallSpectrum017.graph DegreeOneSmallSpectrum021.graph
    sourceMap2053 fusedMap2053 sourceMap2053_checked fusedMap2053_checked
    DegreeTwoThreeFiniteComparisons.comparison2053
#print axioms sourceMap2053_checked
#print axioms fusedMap2053_checked
#print axioms certified2053
def sourceMap2053swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,2,3,0,5,6,7,4] (sourceLabel 2 3 0 v)
def fusedMap2053swap : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![2,3,4,1,0,5,6,7] (fusedLabel 2 3 0 v)
theorem sourceMap2053swap_checked : acceptsGraphIso
    (source (graph core2053) (root 2) 3 0) DegreeOneSmallSpectrum017.graph sourceMap2053swap=true := by decide +kernel
theorem fusedMap2053swap_checked : acceptsGraphIso
    (fused (graph core2053) (root 2) 3 0) DegreeOneSmallSpectrum021.graph fusedMap2053swap=true := by decide +kernel
theorem certified2053swap : Certified (graph core2053) (root 2) 3 0 :=
  of_native_maps core2053 DegreeOneSmallSpectrum017.graph DegreeOneSmallSpectrum021.graph
    sourceMap2053swap fusedMap2053swap sourceMap2053swap_checked fusedMap2053swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2053
#print axioms sourceMap2053swap_checked
#print axioms fusedMap2053swap_checked
#print axioms certified2053swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
