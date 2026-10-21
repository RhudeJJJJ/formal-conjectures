/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0579 : Family 7 := level7.get ⟨30,by decide⟩
def sourceMap0579 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (sourceLabel 7 0 0 v)
def fusedMap0579 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0579_checked : acceptsGraphIso
    (source (graph core0579) (root 7) 0 0) DegreeOneSmallSpectrum109.graph sourceMap0579=true := by decide +kernel
theorem fusedMap0579_checked : acceptsGraphIso
    (fused (graph core0579) (root 7) 0 0) DegreeOneSmallSpectrum111.graph fusedMap0579=true := by decide +kernel
theorem certified0579 : Certified (graph core0579) (root 7) 0 0 :=
  of_native_maps core0579 DegreeOneSmallSpectrum109.graph DegreeOneSmallSpectrum111.graph
    sourceMap0579 fusedMap0579 sourceMap0579_checked fusedMap0579_checked
    DegreeOneSmallComparisons.comparison0579
#print axioms sourceMap0579_checked
#print axioms fusedMap0579_checked
#print axioms certified0579
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
