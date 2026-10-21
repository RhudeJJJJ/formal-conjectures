/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0089 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0089 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 3 2 2 v)
def fusedMap0089 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 2 2 v)
theorem sourceMap0089_checked : acceptsGraphIso
    (source (graph core0089) (root 3) 2 2) DegreeOneSmallSpectrum147.graph sourceMap0089=true := by decide +kernel
theorem fusedMap0089_checked : acceptsGraphIso
    (fused (graph core0089) (root 3) 2 2) DegreeOneSmallSpectrum080.graph fusedMap0089=true := by decide +kernel
theorem certified0089 : Certified (graph core0089) (root 3) 2 2 :=
  of_native_maps core0089 DegreeOneSmallSpectrum147.graph DegreeOneSmallSpectrum080.graph
    sourceMap0089 fusedMap0089 sourceMap0089_checked fusedMap0089_checked
    DegreeOneSmallComparisons.comparison0089
#print axioms sourceMap0089_checked
#print axioms fusedMap0089_checked
#print axioms certified0089
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
