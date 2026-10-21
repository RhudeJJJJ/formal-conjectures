/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0743 : Family 8 := level8.get ⟨2,by decide⟩
def sourceMap0743 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,6,7,8,9,10,4,5] (sourceLabel 8 0 0 v)
def fusedMap0743 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0743_checked : acceptsGraphIso
    (source (graph core0743) (root 8) 0 0) DegreeOneSmallSpectrum193.graph sourceMap0743=true := by decide +kernel
theorem fusedMap0743_checked : acceptsGraphIso
    (fused (graph core0743) (root 8) 0 0) DegreeOneSmallSpectrum165.graph fusedMap0743=true := by decide +kernel
theorem certified0743 : Certified (graph core0743) (root 8) 0 0 :=
  of_native_maps core0743 DegreeOneSmallSpectrum193.graph DegreeOneSmallSpectrum165.graph
    sourceMap0743 fusedMap0743 sourceMap0743_checked fusedMap0743_checked
    DegreeOneSmallComparisons.comparison0743
#print axioms sourceMap0743_checked
#print axioms fusedMap0743_checked
#print axioms certified0743
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
