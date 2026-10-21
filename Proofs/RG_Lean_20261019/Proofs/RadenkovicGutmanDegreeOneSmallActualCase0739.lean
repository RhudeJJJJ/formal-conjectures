/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0739 : Family 8 := level8.get ⟨1,by decide⟩
def sourceMap0739 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,6,7,8,9,10,4,5] (sourceLabel 8 0 0 v)
def fusedMap0739 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0739_checked : acceptsGraphIso
    (source (graph core0739) (root 8) 0 0) DegreeOneSmallSpectrum189.graph sourceMap0739=true := by decide +kernel
theorem fusedMap0739_checked : acceptsGraphIso
    (fused (graph core0739) (root 8) 0 0) DegreeOneSmallSpectrum164.graph fusedMap0739=true := by decide +kernel
theorem certified0739 : Certified (graph core0739) (root 8) 0 0 :=
  of_native_maps core0739 DegreeOneSmallSpectrum189.graph DegreeOneSmallSpectrum164.graph
    sourceMap0739 fusedMap0739 sourceMap0739_checked fusedMap0739_checked
    DegreeOneSmallComparisons.comparison0739
#print axioms sourceMap0739_checked
#print axioms fusedMap0739_checked
#print axioms certified0739
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
