/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0577 : Family 7 := level7.get ⟨28,by decide⟩
def sourceMap0577 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 7 1 1 v)
def fusedMap0577 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0577_checked : acceptsGraphIso
    (source (graph core0577) (root 7) 1 1) DegreeOneSmallSpectrum666.graph sourceMap0577=true := by decide +kernel
theorem fusedMap0577_checked : acceptsGraphIso
    (fused (graph core0577) (root 7) 1 1) DegreeOneSmallSpectrum417.graph fusedMap0577=true := by decide +kernel
theorem certified0577 : Certified (graph core0577) (root 7) 1 1 :=
  of_native_maps core0577 DegreeOneSmallSpectrum666.graph DegreeOneSmallSpectrum417.graph
    sourceMap0577 fusedMap0577 sourceMap0577_checked fusedMap0577_checked
    DegreeOneSmallComparisons.comparison0577
#print axioms sourceMap0577_checked
#print axioms fusedMap0577_checked
#print axioms certified0577
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
