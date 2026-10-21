/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0747 : Family 8 := level8.get ⟨3,by decide⟩
def sourceMap0747 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,6,7,8,9,10,4,5] (sourceLabel 8 0 0 v)
def fusedMap0747 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0747_checked : acceptsGraphIso
    (source (graph core0747) (root 8) 0 0) DegreeOneSmallSpectrum196.graph sourceMap0747=true := by decide +kernel
theorem fusedMap0747_checked : acceptsGraphIso
    (fused (graph core0747) (root 8) 0 0) DegreeOneSmallSpectrum166.graph fusedMap0747=true := by decide +kernel
theorem certified0747 : Certified (graph core0747) (root 8) 0 0 :=
  of_native_maps core0747 DegreeOneSmallSpectrum196.graph DegreeOneSmallSpectrum166.graph
    sourceMap0747 fusedMap0747 sourceMap0747_checked fusedMap0747_checked
    DegreeOneSmallComparisons.comparison0747
#print axioms sourceMap0747_checked
#print axioms fusedMap0747_checked
#print axioms certified0747
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
