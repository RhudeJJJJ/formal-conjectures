/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0891 : Family 8 := level8.get ⟨53,by decide⟩
def sourceMap0891 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (sourceLabel 8 0 0 v)
def fusedMap0891 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0891_checked : acceptsGraphIso
    (source (graph core0891) (root 8) 0 0) DegreeOneSmallSpectrum305.graph sourceMap0891=true := by decide +kernel
theorem fusedMap0891_checked : acceptsGraphIso
    (fused (graph core0891) (root 8) 0 0) DegreeOneSmallSpectrum198.graph fusedMap0891=true := by decide +kernel
theorem certified0891 : Certified (graph core0891) (root 8) 0 0 :=
  of_native_maps core0891 DegreeOneSmallSpectrum305.graph DegreeOneSmallSpectrum198.graph
    sourceMap0891 fusedMap0891 sourceMap0891_checked fusedMap0891_checked
    DegreeOneSmallComparisons.comparison0891
#print axioms sourceMap0891_checked
#print axioms fusedMap0891_checked
#print axioms certified0891
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
