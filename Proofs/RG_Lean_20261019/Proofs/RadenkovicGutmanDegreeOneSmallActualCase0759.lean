/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0759 : Family 8 := level8.get ⟨6,by decide⟩
def sourceMap0759 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,2,1,0,7,8,9,10,6,4,5] (sourceLabel 8 0 0 v)
def fusedMap0759 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0759_checked : acceptsGraphIso
    (source (graph core0759) (root 8) 0 0) DegreeOneSmallSpectrum182.graph sourceMap0759=true := by decide +kernel
theorem fusedMap0759_checked : acceptsGraphIso
    (fused (graph core0759) (root 8) 0 0) DegreeOneSmallSpectrum166.graph fusedMap0759=true := by decide +kernel
theorem certified0759 : Certified (graph core0759) (root 8) 0 0 :=
  of_native_maps core0759 DegreeOneSmallSpectrum182.graph DegreeOneSmallSpectrum166.graph
    sourceMap0759 fusedMap0759 sourceMap0759_checked fusedMap0759_checked
    DegreeOneSmallComparisons.comparison0759
#print axioms sourceMap0759_checked
#print axioms fusedMap0759_checked
#print axioms certified0759
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
