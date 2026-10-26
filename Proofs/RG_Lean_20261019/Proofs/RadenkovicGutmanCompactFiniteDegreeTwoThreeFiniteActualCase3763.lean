/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3763 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3763 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,4,5,2,3,0,6,7,8,9] (sourceLabel 2 1 4 v)
def fusedMap3763 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 1 4 v)
theorem sourceMap3763_checked : acceptsGraphIso
    (source (graph core3763) (root 2) 1 4) DegreeOneSmallSpectrum082.graph sourceMap3763=true := by decide +kernel
theorem fusedMap3763_checked : acceptsGraphIso
    (fused (graph core3763) (root 2) 1 4) DegreeOneSmallSpectrum080.graph fusedMap3763=true := by decide +kernel
theorem certified3763 : Certified (graph core3763) (root 2) 1 4 :=
  of_native_maps core3763 DegreeOneSmallSpectrum082.graph DegreeOneSmallSpectrum080.graph
    sourceMap3763 fusedMap3763 sourceMap3763_checked fusedMap3763_checked
    DegreeTwoThreeFiniteComparisons.comparison3763
#print axioms sourceMap3763_checked
#print axioms fusedMap3763_checked
#print axioms certified3763
def sourceMap3763swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,4,5,0,6,7,8,9,2,3] (sourceLabel 2 4 1 v)
def fusedMap3763swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 4 1 v)
theorem sourceMap3763swap_checked : acceptsGraphIso
    (source (graph core3763) (root 2) 4 1) DegreeOneSmallSpectrum082.graph sourceMap3763swap=true := by decide +kernel
theorem fusedMap3763swap_checked : acceptsGraphIso
    (fused (graph core3763) (root 2) 4 1) DegreeOneSmallSpectrum080.graph fusedMap3763swap=true := by decide +kernel
theorem certified3763swap : Certified (graph core3763) (root 2) 4 1 :=
  of_native_maps core3763 DegreeOneSmallSpectrum082.graph DegreeOneSmallSpectrum080.graph
    sourceMap3763swap fusedMap3763swap sourceMap3763swap_checked fusedMap3763swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3763
#print axioms sourceMap3763swap_checked
#print axioms fusedMap3763swap_checked
#print axioms certified3763swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
