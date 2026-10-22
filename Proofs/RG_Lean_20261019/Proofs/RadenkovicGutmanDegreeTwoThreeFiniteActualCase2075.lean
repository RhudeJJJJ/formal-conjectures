/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2075 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap2075 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2075 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2075_checked : acceptsGraphIso
    (source (graph core2075) (root 6) 0 4) DegreeOneSmallSpectrum1374.graph sourceMap2075=true := by decide +kernel
theorem fusedMap2075_checked : acceptsGraphIso
    (fused (graph core2075) (root 6) 0 4) DegreeOneSmallSpectrum917.graph fusedMap2075=true := by decide +kernel
theorem certified2075 : Certified (graph core2075) (root 6) 0 4 :=
  of_native_maps core2075 DegreeOneSmallSpectrum1374.graph DegreeOneSmallSpectrum917.graph
    sourceMap2075 fusedMap2075 sourceMap2075_checked fusedMap2075_checked
    DegreeTwoThreeFiniteComparisons.comparison2075
#print axioms sourceMap2075_checked
#print axioms fusedMap2075_checked
#print axioms certified2075
def sourceMap2075swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2075swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2075swap_checked : acceptsGraphIso
    (source (graph core2075) (root 6) 4 0) DegreeOneSmallSpectrum1374.graph sourceMap2075swap=true := by decide +kernel
theorem fusedMap2075swap_checked : acceptsGraphIso
    (fused (graph core2075) (root 6) 4 0) DegreeOneSmallSpectrum917.graph fusedMap2075swap=true := by decide +kernel
theorem certified2075swap : Certified (graph core2075) (root 6) 4 0 :=
  of_native_maps core2075 DegreeOneSmallSpectrum1374.graph DegreeOneSmallSpectrum917.graph
    sourceMap2075swap fusedMap2075swap sourceMap2075swap_checked fusedMap2075swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2075
#print axioms sourceMap2075swap_checked
#print axioms fusedMap2075swap_checked
#print axioms certified2075swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
