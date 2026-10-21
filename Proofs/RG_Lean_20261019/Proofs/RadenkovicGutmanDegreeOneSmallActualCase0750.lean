/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0750 : Family 8 := level8.get ⟨3,by decide⟩
def sourceMap0750 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0750 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0750_checked : acceptsGraphIso
    (source (graph core0750) (root 8) 1 1) DegreeOneSmallSpectrum913.graph sourceMap0750=true := by decide +kernel
theorem fusedMap0750_checked : acceptsGraphIso
    (fused (graph core0750) (root 8) 1 1) DegreeOneSmallSpectrum858.graph fusedMap0750=true := by decide +kernel
theorem certified0750 : Certified (graph core0750) (root 8) 1 1 :=
  of_native_maps core0750 DegreeOneSmallSpectrum913.graph DegreeOneSmallSpectrum858.graph
    sourceMap0750 fusedMap0750 sourceMap0750_checked fusedMap0750_checked
    DegreeOneSmallComparisons.comparison0750
#print axioms sourceMap0750_checked
#print axioms fusedMap0750_checked
#print axioms certified0750
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
