/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0090 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0090 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,4,5,6,1,2,3,7,8,9,10] (sourceLabel 3 2 3 v)
def fusedMap0090 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 2 3 v)
theorem sourceMap0090_checked : acceptsGraphIso
    (source (graph core0090) (root 3) 2 3) DegreeOneSmallSpectrum219.graph sourceMap0090=true := by decide +kernel
theorem fusedMap0090_checked : acceptsGraphIso
    (fused (graph core0090) (root 3) 2 3) DegreeOneSmallSpectrum164.graph fusedMap0090=true := by decide +kernel
theorem certified0090 : Certified (graph core0090) (root 3) 2 3 :=
  of_native_maps core0090 DegreeOneSmallSpectrum219.graph DegreeOneSmallSpectrum164.graph
    sourceMap0090 fusedMap0090 sourceMap0090_checked fusedMap0090_checked
    DegreeOneSmallComparisons.comparison0090
#print axioms sourceMap0090_checked
#print axioms fusedMap0090_checked
#print axioms certified0090
def sourceMap0090swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,4,5,6,7,8,9,10,1,2,3] (sourceLabel 3 3 2 v)
def fusedMap0090swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 3 2 v)
theorem sourceMap0090swap_checked : acceptsGraphIso
    (source (graph core0090) (root 3) 3 2) DegreeOneSmallSpectrum219.graph sourceMap0090swap=true := by decide +kernel
theorem fusedMap0090swap_checked : acceptsGraphIso
    (fused (graph core0090) (root 3) 3 2) DegreeOneSmallSpectrum164.graph fusedMap0090swap=true := by decide +kernel
theorem certified0090swap : Certified (graph core0090) (root 3) 3 2 :=
  of_native_maps core0090 DegreeOneSmallSpectrum219.graph DegreeOneSmallSpectrum164.graph
    sourceMap0090swap fusedMap0090swap sourceMap0090swap_checked fusedMap0090swap_checked
    DegreeOneSmallComparisons.comparison0090
#print axioms sourceMap0090swap_checked
#print axioms fusedMap0090swap_checked
#print axioms certified0090swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
