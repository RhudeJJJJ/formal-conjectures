/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0290 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0290 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0290 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0290_checked : acceptsGraphIso
    (source (graph core0290) (root 6) 1 1) DegreeOneSmallSpectrum200.graph sourceMap0290=true := by decide +kernel
theorem fusedMap0290_checked : acceptsGraphIso
    (fused (graph core0290) (root 6) 1 1) DegreeOneSmallSpectrum165.graph fusedMap0290=true := by decide +kernel
theorem certified0290 : Certified (graph core0290) (root 6) 1 1 :=
  of_native_maps core0290 DegreeOneSmallSpectrum200.graph DegreeOneSmallSpectrum165.graph
    sourceMap0290 fusedMap0290 sourceMap0290_checked fusedMap0290_checked
    DegreeOneSmallComparisons.comparison0290
#print axioms sourceMap0290_checked
#print axioms fusedMap0290_checked
#print axioms certified0290
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
