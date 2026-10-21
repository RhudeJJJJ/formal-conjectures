/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0863 : Family 8 := level8.get ⟨41,by decide⟩
def sourceMap0863 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap0863 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0863_checked : acceptsGraphIso
    (source (graph core0863) (root 8) 0 0) DegreeOneSmallSpectrum293.graph sourceMap0863=true := by decide +kernel
theorem fusedMap0863_checked : acceptsGraphIso
    (fused (graph core0863) (root 8) 0 0) DegreeOneSmallSpectrum178.graph fusedMap0863=true := by decide +kernel
theorem certified0863 : Certified (graph core0863) (root 8) 0 0 :=
  of_native_maps core0863 DegreeOneSmallSpectrum293.graph DegreeOneSmallSpectrum178.graph
    sourceMap0863 fusedMap0863 sourceMap0863_checked fusedMap0863_checked
    DegreeOneSmallComparisons.comparison0863
#print axioms sourceMap0863_checked
#print axioms fusedMap0863_checked
#print axioms certified0863
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
