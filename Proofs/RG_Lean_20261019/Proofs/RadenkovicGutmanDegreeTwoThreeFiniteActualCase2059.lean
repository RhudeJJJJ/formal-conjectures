/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2059 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap2059 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap2059 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap2059_checked : acceptsGraphIso
    (source (graph core2059) (root 4) 0 4) DegreeOneSmallSpectrum198.graph sourceMap2059=true := by decide +kernel
theorem fusedMap2059_checked : acceptsGraphIso
    (fused (graph core2059) (root 4) 0 4) DegreeOneSmallSpectrum202.graph fusedMap2059=true := by decide +kernel
theorem certified2059 : Certified (graph core2059) (root 4) 0 4 :=
  of_native_maps core2059 DegreeOneSmallSpectrum198.graph DegreeOneSmallSpectrum202.graph
    sourceMap2059 fusedMap2059 sourceMap2059_checked fusedMap2059_checked
    DegreeTwoThreeFiniteComparisons.comparison2059
#print axioms sourceMap2059_checked
#print axioms fusedMap2059_checked
#print axioms certified2059
def sourceMap2059swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap2059swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap2059swap_checked : acceptsGraphIso
    (source (graph core2059) (root 4) 4 0) DegreeOneSmallSpectrum198.graph sourceMap2059swap=true := by decide +kernel
theorem fusedMap2059swap_checked : acceptsGraphIso
    (fused (graph core2059) (root 4) 4 0) DegreeOneSmallSpectrum202.graph fusedMap2059swap=true := by decide +kernel
theorem certified2059swap : Certified (graph core2059) (root 4) 4 0 :=
  of_native_maps core2059 DegreeOneSmallSpectrum198.graph DegreeOneSmallSpectrum202.graph
    sourceMap2059swap fusedMap2059swap sourceMap2059swap_checked fusedMap2059swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2059
#print axioms sourceMap2059swap_checked
#print axioms fusedMap2059swap_checked
#print axioms certified2059swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
