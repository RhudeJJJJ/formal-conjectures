/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0250 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0250 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0250 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0250_checked : acceptsGraphIso
    (source (graph core0250) (root 5) 1 2) DegreeOneSmallSpectrum337.graph sourceMap0250=true := by decide +kernel
theorem fusedMap0250_checked : acceptsGraphIso
    (fused (graph core0250) (root 5) 1 2) DegreeOneSmallSpectrum207.graph fusedMap0250=true := by decide +kernel
theorem certified0250 : Certified (graph core0250) (root 5) 1 2 :=
  of_native_maps core0250 DegreeOneSmallSpectrum337.graph DegreeOneSmallSpectrum207.graph
    sourceMap0250 fusedMap0250 sourceMap0250_checked fusedMap0250_checked
    DegreeOneSmallComparisons.comparison0250
#print axioms sourceMap0250_checked
#print axioms fusedMap0250_checked
#print axioms certified0250
def sourceMap0250swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0250swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0250swap_checked : acceptsGraphIso
    (source (graph core0250) (root 5) 2 1) DegreeOneSmallSpectrum337.graph sourceMap0250swap=true := by decide +kernel
theorem fusedMap0250swap_checked : acceptsGraphIso
    (fused (graph core0250) (root 5) 2 1) DegreeOneSmallSpectrum207.graph fusedMap0250swap=true := by decide +kernel
theorem certified0250swap : Certified (graph core0250) (root 5) 2 1 :=
  of_native_maps core0250 DegreeOneSmallSpectrum337.graph DegreeOneSmallSpectrum207.graph
    sourceMap0250swap fusedMap0250swap sourceMap0250swap_checked fusedMap0250swap_checked
    DegreeOneSmallComparisons.comparison0250
#print axioms sourceMap0250swap_checked
#print axioms fusedMap0250swap_checked
#print axioms certified0250swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
