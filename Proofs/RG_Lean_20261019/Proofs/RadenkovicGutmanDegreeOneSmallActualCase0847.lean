/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0847 : Family 8 := level8.get ⟨36,by decide⟩
def sourceMap0847 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap0847 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0847_checked : acceptsGraphIso
    (source (graph core0847) (root 8) 0 0) DegreeOneSmallSpectrum262.graph sourceMap0847=true := by decide +kernel
theorem fusedMap0847_checked : acceptsGraphIso
    (fused (graph core0847) (root 8) 0 0) DegreeOneSmallSpectrum171.graph fusedMap0847=true := by decide +kernel
theorem certified0847 : Certified (graph core0847) (root 8) 0 0 :=
  of_native_maps core0847 DegreeOneSmallSpectrum262.graph DegreeOneSmallSpectrum171.graph
    sourceMap0847 fusedMap0847 sourceMap0847_checked fusedMap0847_checked
    DegreeOneSmallComparisons.comparison0847
#print axioms sourceMap0847_checked
#print axioms fusedMap0847_checked
#print axioms certified0847
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
