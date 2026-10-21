/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0950 : Family 8 := level8.get ⟨73,by decide⟩
def sourceMap0950 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0950 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0950_checked : acceptsGraphIso
    (source (graph core0950) (root 8) 1 1) DegreeOneSmallSpectrum1328.graph sourceMap0950=true := by decide +kernel
theorem fusedMap0950_checked : acceptsGraphIso
    (fused (graph core0950) (root 8) 1 1) DegreeOneSmallSpectrum948.graph fusedMap0950=true := by decide +kernel
theorem certified0950 : Certified (graph core0950) (root 8) 1 1 :=
  of_native_maps core0950 DegreeOneSmallSpectrum1328.graph DegreeOneSmallSpectrum948.graph
    sourceMap0950 fusedMap0950 sourceMap0950_checked fusedMap0950_checked
    DegreeOneSmallComparisons.comparison0950
#print axioms sourceMap0950_checked
#print axioms fusedMap0950_checked
#print axioms certified0950
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
