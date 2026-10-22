/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0743 : Family 10 := level10.get ⟨377,by decide⟩
def sourceMap0743 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0743 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0743_checked : acceptsGraphIso
    (source (graph core0743) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1901.graph sourceMap0743=true := by decide +kernel
theorem fusedMap0743_checked : acceptsGraphIso
    (fused (graph core0743) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1410.graph fusedMap0743=true := by decide +kernel
theorem certified0743 : Certified (graph core0743) (root 10) 2 2 :=
  of_native_maps core0743 DegreeOneMiddleResidualSpectrum1901.graph DegreeOneMiddleResidualSpectrum1410.graph
    sourceMap0743 fusedMap0743 sourceMap0743_checked fusedMap0743_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0743
#print axioms sourceMap0743_checked
#print axioms fusedMap0743_checked
#print axioms certified0743
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
