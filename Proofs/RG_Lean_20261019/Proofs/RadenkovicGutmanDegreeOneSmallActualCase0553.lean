/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0553 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0553 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,6,7,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0553 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0553_checked : acceptsGraphIso
    (source (graph core0553) (root 7) 1 1) DegreeOneSmallSpectrum506.graph sourceMap0553=true := by decide +kernel
theorem fusedMap0553_checked : acceptsGraphIso
    (fused (graph core0553) (root 7) 1 1) DegreeOneSmallSpectrum393.graph fusedMap0553=true := by decide +kernel
theorem certified0553 : Certified (graph core0553) (root 7) 1 1 :=
  of_native_maps core0553 DegreeOneSmallSpectrum506.graph DegreeOneSmallSpectrum393.graph
    sourceMap0553 fusedMap0553 sourceMap0553_checked fusedMap0553_checked
    DegreeOneSmallComparisons.comparison0553
#print axioms sourceMap0553_checked
#print axioms fusedMap0553_checked
#print axioms certified0553
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
