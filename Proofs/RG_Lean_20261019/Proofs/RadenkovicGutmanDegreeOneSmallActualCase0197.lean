/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0197 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0197 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,4,1,2,3] (sourceLabel 5 0 2 v)
def fusedMap0197 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0197_checked : acceptsGraphIso
    (source (graph core0197) (root 5) 0 2) DegreeOneSmallSpectrum089.graph sourceMap0197=true := by decide +kernel
theorem fusedMap0197_checked : acceptsGraphIso
    (fused (graph core0197) (root 5) 0 2) DegreeOneSmallSpectrum090.graph fusedMap0197=true := by decide +kernel
theorem certified0197 : Certified (graph core0197) (root 5) 0 2 :=
  of_native_maps core0197 DegreeOneSmallSpectrum089.graph DegreeOneSmallSpectrum090.graph
    sourceMap0197 fusedMap0197 sourceMap0197_checked fusedMap0197_checked
    DegreeOneSmallComparisons.comparison0197
#print axioms sourceMap0197_checked
#print axioms fusedMap0197_checked
#print axioms certified0197
def sourceMap0197swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 5 2 0 v)
def fusedMap0197swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0197swap_checked : acceptsGraphIso
    (source (graph core0197) (root 5) 2 0) DegreeOneSmallSpectrum089.graph sourceMap0197swap=true := by decide +kernel
theorem fusedMap0197swap_checked : acceptsGraphIso
    (fused (graph core0197) (root 5) 2 0) DegreeOneSmallSpectrum090.graph fusedMap0197swap=true := by decide +kernel
theorem certified0197swap : Certified (graph core0197) (root 5) 2 0 :=
  of_native_maps core0197 DegreeOneSmallSpectrum089.graph DegreeOneSmallSpectrum090.graph
    sourceMap0197swap fusedMap0197swap sourceMap0197swap_checked fusedMap0197swap_checked
    DegreeOneSmallComparisons.comparison0197
#print axioms sourceMap0197swap_checked
#print axioms fusedMap0197swap_checked
#print axioms certified0197swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
