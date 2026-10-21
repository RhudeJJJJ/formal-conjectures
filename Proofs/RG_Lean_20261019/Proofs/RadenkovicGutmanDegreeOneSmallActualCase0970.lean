/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0970 : Family 8 := level8.get ⟨83,by decide⟩
def sourceMap0970 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0970 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0970_checked : acceptsGraphIso
    (source (graph core0970) (root 8) 1 1) DegreeOneSmallSpectrum1314.graph sourceMap0970=true := by decide +kernel
theorem fusedMap0970_checked : acceptsGraphIso
    (fused (graph core0970) (root 8) 1 1) DegreeOneSmallSpectrum967.graph fusedMap0970=true := by decide +kernel
theorem certified0970 : Certified (graph core0970) (root 8) 1 1 :=
  of_native_maps core0970 DegreeOneSmallSpectrum1314.graph DegreeOneSmallSpectrum967.graph
    sourceMap0970 fusedMap0970 sourceMap0970_checked fusedMap0970_checked
    DegreeOneSmallComparisons.comparison0970
#print axioms sourceMap0970_checked
#print axioms fusedMap0970_checked
#print axioms certified0970
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
