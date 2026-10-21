/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0609 : Family 7 := level7.get ⟨39,by decide⟩
def sourceMap0609 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0609 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0609_checked : acceptsGraphIso
    (source (graph core0609) (root 7) 0 0) DegreeOneSmallSpectrum123.graph sourceMap0609=true := by decide +kernel
theorem fusedMap0609_checked : acceptsGraphIso
    (fused (graph core0609) (root 7) 0 0) DegreeOneSmallSpectrum133.graph fusedMap0609=true := by decide +kernel
theorem certified0609 : Certified (graph core0609) (root 7) 0 0 :=
  of_native_maps core0609 DegreeOneSmallSpectrum123.graph DegreeOneSmallSpectrum133.graph
    sourceMap0609 fusedMap0609 sourceMap0609_checked fusedMap0609_checked
    DegreeOneSmallComparisons.comparison0609
#print axioms sourceMap0609_checked
#print axioms fusedMap0609_checked
#print axioms certified0609
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
