/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0559 : Family 7 := level7.get ⟨22,by decide⟩
def sourceMap0559 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0559 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0559_checked : acceptsGraphIso
    (source (graph core0559) (root 7) 1 1) DegreeOneSmallSpectrum507.graph sourceMap0559=true := by decide +kernel
theorem fusedMap0559_checked : acceptsGraphIso
    (fused (graph core0559) (root 7) 1 1) DegreeOneSmallSpectrum394.graph fusedMap0559=true := by decide +kernel
theorem certified0559 : Certified (graph core0559) (root 7) 1 1 :=
  of_native_maps core0559 DegreeOneSmallSpectrum507.graph DegreeOneSmallSpectrum394.graph
    sourceMap0559 fusedMap0559 sourceMap0559_checked fusedMap0559_checked
    DegreeOneSmallComparisons.comparison0559
#print axioms sourceMap0559_checked
#print axioms fusedMap0559_checked
#print axioms certified0559
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
