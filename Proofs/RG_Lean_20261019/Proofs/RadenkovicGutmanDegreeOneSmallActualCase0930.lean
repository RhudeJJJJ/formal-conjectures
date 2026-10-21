/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0930 : Family 8 := level8.get ⟨65,by decide⟩
def sourceMap0930 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,6,7,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0930 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0930_checked : acceptsGraphIso
    (source (graph core0930) (root 8) 1 1) DegreeOneSmallSpectrum1317.graph sourceMap0930=true := by decide +kernel
theorem fusedMap0930_checked : acceptsGraphIso
    (fused (graph core0930) (root 8) 1 1) DegreeOneSmallSpectrum930.graph fusedMap0930=true := by decide +kernel
theorem certified0930 : Certified (graph core0930) (root 8) 1 1 :=
  of_native_maps core0930 DegreeOneSmallSpectrum1317.graph DegreeOneSmallSpectrum930.graph
    sourceMap0930 fusedMap0930 sourceMap0930_checked fusedMap0930_checked
    DegreeOneSmallComparisons.comparison0930
#print axioms sourceMap0930_checked
#print axioms fusedMap0930_checked
#print axioms certified0930
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
