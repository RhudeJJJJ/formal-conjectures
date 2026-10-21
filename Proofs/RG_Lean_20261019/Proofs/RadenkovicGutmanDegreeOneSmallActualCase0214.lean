/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0214 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0214 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0214 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0214_checked : acceptsGraphIso
    (source (graph core0214) (root 5) 1 2) DegreeOneSmallSpectrum265.graph sourceMap0214=true := by decide +kernel
theorem fusedMap0214_checked : acceptsGraphIso
    (fused (graph core0214) (root 5) 1 2) DegreeOneSmallSpectrum175.graph fusedMap0214=true := by decide +kernel
theorem certified0214 : Certified (graph core0214) (root 5) 1 2 :=
  of_native_maps core0214 DegreeOneSmallSpectrum265.graph DegreeOneSmallSpectrum175.graph
    sourceMap0214 fusedMap0214 sourceMap0214_checked fusedMap0214_checked
    DegreeOneSmallComparisons.comparison0214
#print axioms sourceMap0214_checked
#print axioms fusedMap0214_checked
#print axioms certified0214
def sourceMap0214swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0214swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0214swap_checked : acceptsGraphIso
    (source (graph core0214) (root 5) 2 1) DegreeOneSmallSpectrum265.graph sourceMap0214swap=true := by decide +kernel
theorem fusedMap0214swap_checked : acceptsGraphIso
    (fused (graph core0214) (root 5) 2 1) DegreeOneSmallSpectrum175.graph fusedMap0214swap=true := by decide +kernel
theorem certified0214swap : Certified (graph core0214) (root 5) 2 1 :=
  of_native_maps core0214 DegreeOneSmallSpectrum265.graph DegreeOneSmallSpectrum175.graph
    sourceMap0214swap fusedMap0214swap sourceMap0214swap_checked fusedMap0214swap_checked
    DegreeOneSmallComparisons.comparison0214
#print axioms sourceMap0214swap_checked
#print axioms fusedMap0214swap_checked
#print axioms certified0214swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
