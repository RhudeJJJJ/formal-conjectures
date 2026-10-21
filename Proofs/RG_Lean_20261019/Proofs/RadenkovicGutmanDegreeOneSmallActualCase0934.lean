/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0934 : Family 8 := level8.get ⟨66,by decide⟩
def sourceMap0934 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0934 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0934_checked : acceptsGraphIso
    (source (graph core0934) (root 8) 1 1) DegreeOneSmallSpectrum1321.graph sourceMap0934=true := by decide +kernel
theorem fusedMap0934_checked : acceptsGraphIso
    (fused (graph core0934) (root 8) 1 1) DegreeOneSmallSpectrum931.graph fusedMap0934=true := by decide +kernel
theorem certified0934 : Certified (graph core0934) (root 8) 1 1 :=
  of_native_maps core0934 DegreeOneSmallSpectrum1321.graph DegreeOneSmallSpectrum931.graph
    sourceMap0934 fusedMap0934 sourceMap0934_checked fusedMap0934_checked
    DegreeOneSmallComparisons.comparison0934
#print axioms sourceMap0934_checked
#print axioms fusedMap0934_checked
#print axioms certified0934
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
