/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0104 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0104 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (sourceLabel 4 1 3 v)
def fusedMap0104 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 1 3 v)
theorem sourceMap0104_checked : acceptsGraphIso
    (source (graph core0104) (root 4) 1 3) DegreeOneSmallSpectrum228.graph sourceMap0104=true := by decide +kernel
theorem fusedMap0104_checked : acceptsGraphIso
    (fused (graph core0104) (root 4) 1 3) DegreeOneSmallSpectrum168.graph fusedMap0104=true := by decide +kernel
theorem certified0104 : Certified (graph core0104) (root 4) 1 3 :=
  of_native_maps core0104 DegreeOneSmallSpectrum228.graph DegreeOneSmallSpectrum168.graph
    sourceMap0104 fusedMap0104 sourceMap0104_checked fusedMap0104_checked
    DegreeOneSmallComparisons.comparison0104
#print axioms sourceMap0104_checked
#print axioms fusedMap0104_checked
#print axioms certified0104
def sourceMap0104swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 3 1 v)
def fusedMap0104swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 3 1 v)
theorem sourceMap0104swap_checked : acceptsGraphIso
    (source (graph core0104) (root 4) 3 1) DegreeOneSmallSpectrum228.graph sourceMap0104swap=true := by decide +kernel
theorem fusedMap0104swap_checked : acceptsGraphIso
    (fused (graph core0104) (root 4) 3 1) DegreeOneSmallSpectrum168.graph fusedMap0104swap=true := by decide +kernel
theorem certified0104swap : Certified (graph core0104) (root 4) 3 1 :=
  of_native_maps core0104 DegreeOneSmallSpectrum228.graph DegreeOneSmallSpectrum168.graph
    sourceMap0104swap fusedMap0104swap sourceMap0104swap_checked fusedMap0104swap_checked
    DegreeOneSmallComparisons.comparison0104
#print axioms sourceMap0104swap_checked
#print axioms fusedMap0104swap_checked
#print axioms certified0104swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
