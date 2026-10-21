/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0879 : Family 8 := level8.get ⟨46,by decide⟩
def sourceMap0879 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0879 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0879_checked : acceptsGraphIso
    (source (graph core0879) (root 8) 0 0) DegreeOneSmallSpectrum293.graph sourceMap0879=true := by decide +kernel
theorem fusedMap0879_checked : acceptsGraphIso
    (fused (graph core0879) (root 8) 0 0) DegreeOneSmallSpectrum187.graph fusedMap0879=true := by decide +kernel
theorem certified0879 : Certified (graph core0879) (root 8) 0 0 :=
  of_native_maps core0879 DegreeOneSmallSpectrum293.graph DegreeOneSmallSpectrum187.graph
    sourceMap0879 fusedMap0879 sourceMap0879_checked fusedMap0879_checked
    DegreeOneSmallComparisons.comparison0879
#print axioms sourceMap0879_checked
#print axioms fusedMap0879_checked
#print axioms certified0879
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
