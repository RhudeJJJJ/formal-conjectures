/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0911 : Family 8 := level8.get ⟨59,by decide⟩
def sourceMap0911 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0911 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0911_checked : acceptsGraphIso
    (source (graph core0911) (root 8) 0 0) DegreeOneSmallSpectrum297.graph sourceMap0911=true := by decide +kernel
theorem fusedMap0911_checked : acceptsGraphIso
    (fused (graph core0911) (root 8) 0 0) DegreeOneSmallSpectrum206.graph fusedMap0911=true := by decide +kernel
theorem certified0911 : Certified (graph core0911) (root 8) 0 0 :=
  of_native_maps core0911 DegreeOneSmallSpectrum297.graph DegreeOneSmallSpectrum206.graph
    sourceMap0911 fusedMap0911 sourceMap0911_checked fusedMap0911_checked
    DegreeOneSmallComparisons.comparison0911
#print axioms sourceMap0911_checked
#print axioms fusedMap0911_checked
#print axioms certified0911
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
