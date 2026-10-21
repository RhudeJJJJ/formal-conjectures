/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0803 : Family 8 := level8.get ⟨20,by decide⟩
def sourceMap0803 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0803 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0803_checked : acceptsGraphIso
    (source (graph core0803) (root 8) 0 0) DegreeOneSmallSpectrum194.graph sourceMap0803=true := by decide +kernel
theorem fusedMap0803_checked : acceptsGraphIso
    (fused (graph core0803) (root 8) 0 0) DegreeOneSmallSpectrum222.graph fusedMap0803=true := by decide +kernel
theorem certified0803 : Certified (graph core0803) (root 8) 0 0 :=
  of_native_maps core0803 DegreeOneSmallSpectrum194.graph DegreeOneSmallSpectrum222.graph
    sourceMap0803 fusedMap0803 sourceMap0803_checked fusedMap0803_checked
    DegreeOneSmallComparisons.comparison0803
#print axioms sourceMap0803_checked
#print axioms fusedMap0803_checked
#print axioms certified0803
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
