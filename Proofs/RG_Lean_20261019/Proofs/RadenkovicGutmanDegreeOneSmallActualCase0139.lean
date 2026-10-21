/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0139 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0139 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 2 2 v)
def fusedMap0139 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap0139_checked : acceptsGraphIso
    (source (graph core0139) (root 4) 2 2) DegreeOneSmallSpectrum341.graph sourceMap0139=true := by decide +kernel
theorem fusedMap0139_checked : acceptsGraphIso
    (fused (graph core0139) (root 4) 2 2) DegreeOneSmallSpectrum165.graph fusedMap0139=true := by decide +kernel
theorem certified0139 : Certified (graph core0139) (root 4) 2 2 :=
  of_native_maps core0139 DegreeOneSmallSpectrum341.graph DegreeOneSmallSpectrum165.graph
    sourceMap0139 fusedMap0139 sourceMap0139_checked fusedMap0139_checked
    DegreeOneSmallComparisons.comparison0139
#print axioms sourceMap0139_checked
#print axioms fusedMap0139_checked
#print axioms certified0139
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
