/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0838 : Family 8 := level8.get ⟨30,by decide⟩
def sourceMap0838 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0838 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 1 1 v)
theorem sourceMap0838_checked : acceptsGraphIso
    (source (graph core0838) (root 8) 1 1) DegreeOneSmallSpectrum1323.graph sourceMap0838=true := by decide +kernel
theorem fusedMap0838_checked : acceptsGraphIso
    (fused (graph core0838) (root 8) 1 1) DegreeOneSmallSpectrum978.graph fusedMap0838=true := by decide +kernel
theorem certified0838 : Certified (graph core0838) (root 8) 1 1 :=
  of_native_maps core0838 DegreeOneSmallSpectrum1323.graph DegreeOneSmallSpectrum978.graph
    sourceMap0838 fusedMap0838 sourceMap0838_checked fusedMap0838_checked
    DegreeOneSmallComparisons.comparison0838
#print axioms sourceMap0838_checked
#print axioms fusedMap0838_checked
#print axioms certified0838
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
