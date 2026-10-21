/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0378 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0378 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0378 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0378_checked : acceptsGraphIso
    (source (graph core0378) (root 6) 0 3) DegreeOneSmallSpectrum581.graph sourceMap0378=true := by decide +kernel
theorem fusedMap0378_checked : acceptsGraphIso
    (fused (graph core0378) (root 6) 0 3) DegreeOneSmallSpectrum388.graph fusedMap0378=true := by decide +kernel
theorem certified0378 : Certified (graph core0378) (root 6) 0 3 :=
  of_native_maps core0378 DegreeOneSmallSpectrum581.graph DegreeOneSmallSpectrum388.graph
    sourceMap0378 fusedMap0378 sourceMap0378_checked fusedMap0378_checked
    DegreeOneSmallComparisons.comparison0378
#print axioms sourceMap0378_checked
#print axioms fusedMap0378_checked
#print axioms certified0378
def sourceMap0378swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0378swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0378swap_checked : acceptsGraphIso
    (source (graph core0378) (root 6) 3 0) DegreeOneSmallSpectrum581.graph sourceMap0378swap=true := by decide +kernel
theorem fusedMap0378swap_checked : acceptsGraphIso
    (fused (graph core0378) (root 6) 3 0) DegreeOneSmallSpectrum388.graph fusedMap0378swap=true := by decide +kernel
theorem certified0378swap : Certified (graph core0378) (root 6) 3 0 :=
  of_native_maps core0378 DegreeOneSmallSpectrum581.graph DegreeOneSmallSpectrum388.graph
    sourceMap0378swap fusedMap0378swap sourceMap0378swap_checked fusedMap0378swap_checked
    DegreeOneSmallComparisons.comparison0378
#print axioms sourceMap0378swap_checked
#print axioms fusedMap0378swap_checked
#print axioms certified0378swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
