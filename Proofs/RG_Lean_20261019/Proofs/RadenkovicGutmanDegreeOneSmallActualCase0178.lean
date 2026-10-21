/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0178 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0178 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0178 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0178_checked : acceptsGraphIso
    (source (graph core0178) (root 5) 1 2) DegreeOneSmallSpectrum194.graph sourceMap0178=true := by decide +kernel
theorem fusedMap0178_checked : acceptsGraphIso
    (fused (graph core0178) (root 5) 1 2) DegreeOneSmallSpectrum164.graph fusedMap0178=true := by decide +kernel
theorem certified0178 : Certified (graph core0178) (root 5) 1 2 :=
  of_native_maps core0178 DegreeOneSmallSpectrum194.graph DegreeOneSmallSpectrum164.graph
    sourceMap0178 fusedMap0178 sourceMap0178_checked fusedMap0178_checked
    DegreeOneSmallComparisons.comparison0178
#print axioms sourceMap0178_checked
#print axioms fusedMap0178_checked
#print axioms certified0178
def sourceMap0178swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0178swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0178swap_checked : acceptsGraphIso
    (source (graph core0178) (root 5) 2 1) DegreeOneSmallSpectrum194.graph sourceMap0178swap=true := by decide +kernel
theorem fusedMap0178swap_checked : acceptsGraphIso
    (fused (graph core0178) (root 5) 2 1) DegreeOneSmallSpectrum164.graph fusedMap0178swap=true := by decide +kernel
theorem certified0178swap : Certified (graph core0178) (root 5) 2 1 :=
  of_native_maps core0178 DegreeOneSmallSpectrum194.graph DegreeOneSmallSpectrum164.graph
    sourceMap0178swap fusedMap0178swap sourceMap0178swap_checked fusedMap0178swap_checked
    DegreeOneSmallComparisons.comparison0178
#print axioms sourceMap0178swap_checked
#print axioms fusedMap0178swap_checked
#print axioms certified0178swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
