/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0477 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0477 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (sourceLabel 7 0 0 v)
def fusedMap0477 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0477_checked : acceptsGraphIso
    (source (graph core0477) (root 7) 0 0) DegreeOneSmallSpectrum075.graph sourceMap0477=true := by decide +kernel
theorem fusedMap0477_checked : acceptsGraphIso
    (fused (graph core0477) (root 7) 0 0) DegreeOneSmallSpectrum090.graph fusedMap0477=true := by decide +kernel
theorem certified0477 : Certified (graph core0477) (root 7) 0 0 :=
  of_native_maps core0477 DegreeOneSmallSpectrum075.graph DegreeOneSmallSpectrum090.graph
    sourceMap0477 fusedMap0477 sourceMap0477_checked fusedMap0477_checked
    DegreeOneSmallComparisons.comparison0477
#print axioms sourceMap0477_checked
#print axioms fusedMap0477_checked
#print axioms certified0477
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
