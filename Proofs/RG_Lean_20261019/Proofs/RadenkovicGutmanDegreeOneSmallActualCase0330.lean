/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0330 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0330 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (sourceLabel 6 0 0 v)
def fusedMap0330 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0330_checked : acceptsGraphIso
    (source (graph core0330) (root 6) 0 0) DegreeOneSmallSpectrum045.graph sourceMap0330=true := by decide +kernel
theorem fusedMap0330_checked : acceptsGraphIso
    (fused (graph core0330) (root 6) 0 0) DegreeOneSmallSpectrum052.graph fusedMap0330=true := by decide +kernel
theorem certified0330 : Certified (graph core0330) (root 6) 0 0 :=
  of_native_maps core0330 DegreeOneSmallSpectrum045.graph DegreeOneSmallSpectrum052.graph
    sourceMap0330 fusedMap0330 sourceMap0330_checked fusedMap0330_checked
    DegreeOneSmallComparisons.comparison0330
#print axioms sourceMap0330_checked
#print axioms fusedMap0330_checked
#print axioms certified0330
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
