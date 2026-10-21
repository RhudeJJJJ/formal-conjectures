/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0758 : Family 8 := level8.get ⟨5,by decide⟩
def sourceMap0758 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0758 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0758_checked : acceptsGraphIso
    (source (graph core0758) (root 8) 1 1) DegreeOneSmallSpectrum911.graph sourceMap0758=true := by decide +kernel
theorem fusedMap0758_checked : acceptsGraphIso
    (fused (graph core0758) (root 8) 1 1) DegreeOneSmallSpectrum860.graph fusedMap0758=true := by decide +kernel
theorem certified0758 : Certified (graph core0758) (root 8) 1 1 :=
  of_native_maps core0758 DegreeOneSmallSpectrum911.graph DegreeOneSmallSpectrum860.graph
    sourceMap0758 fusedMap0758 sourceMap0758_checked fusedMap0758_checked
    DegreeOneSmallComparisons.comparison0758
#print axioms sourceMap0758_checked
#print axioms fusedMap0758_checked
#print axioms certified0758
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
