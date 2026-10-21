/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0177 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0177 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 5 1 1 v)
def fusedMap0177 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0177_checked : acceptsGraphIso
    (source (graph core0177) (root 5) 1 1) DegreeOneSmallSpectrum124.graph sourceMap0177=true := by decide +kernel
theorem fusedMap0177_checked : acceptsGraphIso
    (fused (graph core0177) (root 5) 1 1) DegreeOneSmallSpectrum080.graph fusedMap0177=true := by decide +kernel
theorem certified0177 : Certified (graph core0177) (root 5) 1 1 :=
  of_native_maps core0177 DegreeOneSmallSpectrum124.graph DegreeOneSmallSpectrum080.graph
    sourceMap0177 fusedMap0177 sourceMap0177_checked fusedMap0177_checked
    DegreeOneSmallComparisons.comparison0177
#print axioms sourceMap0177_checked
#print axioms fusedMap0177_checked
#print axioms certified0177
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
