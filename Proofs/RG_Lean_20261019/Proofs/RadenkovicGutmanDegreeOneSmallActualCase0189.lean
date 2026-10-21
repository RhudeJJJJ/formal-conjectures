/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0189 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0189 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 5 1 1 v)
def fusedMap0189 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0189_checked : acceptsGraphIso
    (source (graph core0189) (root 5) 1 1) DegreeOneSmallSpectrum136.graph sourceMap0189=true := by decide +kernel
theorem fusedMap0189_checked : acceptsGraphIso
    (fused (graph core0189) (root 5) 1 1) DegreeOneSmallSpectrum086.graph fusedMap0189=true := by decide +kernel
theorem certified0189 : Certified (graph core0189) (root 5) 1 1 :=
  of_native_maps core0189 DegreeOneSmallSpectrum136.graph DegreeOneSmallSpectrum086.graph
    sourceMap0189 fusedMap0189 sourceMap0189_checked fusedMap0189_checked
    DegreeOneSmallComparisons.comparison0189
#print axioms sourceMap0189_checked
#print axioms fusedMap0189_checked
#print axioms certified0189
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
