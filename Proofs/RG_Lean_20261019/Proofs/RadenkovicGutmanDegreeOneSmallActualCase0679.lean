/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0679 : Family 7 := level7.get ⟨63,by decide⟩
def sourceMap0679 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0679 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0679_checked : acceptsGraphIso
    (source (graph core0679) (root 7) 1 1) DegreeOneSmallSpectrum615.graph sourceMap0679=true := by decide +kernel
theorem fusedMap0679_checked : acceptsGraphIso
    (fused (graph core0679) (root 7) 1 1) DegreeOneSmallSpectrum399.graph fusedMap0679=true := by decide +kernel
theorem certified0679 : Certified (graph core0679) (root 7) 1 1 :=
  of_native_maps core0679 DegreeOneSmallSpectrum615.graph DegreeOneSmallSpectrum399.graph
    sourceMap0679 fusedMap0679 sourceMap0679_checked fusedMap0679_checked
    DegreeOneSmallComparisons.comparison0679
#print axioms sourceMap0679_checked
#print axioms fusedMap0679_checked
#print axioms certified0679
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
