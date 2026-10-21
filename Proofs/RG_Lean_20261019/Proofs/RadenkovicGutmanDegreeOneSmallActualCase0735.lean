/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0735 : Family 8 := level8.get ⟨0,by decide⟩
def sourceMap0735 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,6,7,8,9,10,4,5] (sourceLabel 8 0 0 v)
def fusedMap0735 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![3,2,1,0,6,7,8,9,10,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0735_checked : acceptsGraphIso
    (source (graph core0735) (root 8) 0 0) DegreeOneSmallSpectrum164.graph sourceMap0735=true := by decide +kernel
theorem fusedMap0735_checked : acceptsGraphIso
    (fused (graph core0735) (root 8) 0 0) DegreeOneSmallSpectrum168.graph fusedMap0735=true := by decide +kernel
theorem certified0735 : Certified (graph core0735) (root 8) 0 0 :=
  of_native_maps core0735 DegreeOneSmallSpectrum164.graph DegreeOneSmallSpectrum168.graph
    sourceMap0735 fusedMap0735 sourceMap0735_checked fusedMap0735_checked
    DegreeOneSmallComparisons.comparison0735
#print axioms sourceMap0735_checked
#print axioms fusedMap0735_checked
#print axioms certified0735
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
