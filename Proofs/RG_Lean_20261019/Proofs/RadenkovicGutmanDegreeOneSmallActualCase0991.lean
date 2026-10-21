/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0991 : Family 8 := level8.get ⟨97,by decide⟩
def sourceMap0991 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap0991 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0991_checked : acceptsGraphIso
    (source (graph core0991) (root 8) 0 0) DegreeOneSmallSpectrum240.graph sourceMap0991=true := by decide +kernel
theorem fusedMap0991_checked : acceptsGraphIso
    (fused (graph core0991) (root 8) 0 0) DegreeOneSmallSpectrum244.graph fusedMap0991=true := by decide +kernel
theorem certified0991 : Certified (graph core0991) (root 8) 0 0 :=
  of_native_maps core0991 DegreeOneSmallSpectrum240.graph DegreeOneSmallSpectrum244.graph
    sourceMap0991 fusedMap0991 sourceMap0991_checked fusedMap0991_checked
    DegreeOneSmallComparisons.comparison0991
#print axioms sourceMap0991_checked
#print axioms fusedMap0991_checked
#print axioms certified0991
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
