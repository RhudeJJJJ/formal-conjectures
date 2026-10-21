/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0222 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0222 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap0222 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0222_checked : acceptsGraphIso
    (source (graph core0222) (root 5) 0 3) DegreeOneSmallSpectrum178.graph sourceMap0222=true := by decide +kernel
theorem fusedMap0222_checked : acceptsGraphIso
    (fused (graph core0222) (root 5) 0 3) DegreeOneSmallSpectrum182.graph fusedMap0222=true := by decide +kernel
theorem certified0222 : Certified (graph core0222) (root 5) 0 3 :=
  of_native_maps core0222 DegreeOneSmallSpectrum178.graph DegreeOneSmallSpectrum182.graph
    sourceMap0222 fusedMap0222 sourceMap0222_checked fusedMap0222_checked
    DegreeOneSmallComparisons.comparison0222
#print axioms sourceMap0222_checked
#print axioms fusedMap0222_checked
#print axioms certified0222
def sourceMap0222swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,6] (sourceLabel 5 3 0 v)
def fusedMap0222swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0222swap_checked : acceptsGraphIso
    (source (graph core0222) (root 5) 3 0) DegreeOneSmallSpectrum178.graph sourceMap0222swap=true := by decide +kernel
theorem fusedMap0222swap_checked : acceptsGraphIso
    (fused (graph core0222) (root 5) 3 0) DegreeOneSmallSpectrum182.graph fusedMap0222swap=true := by decide +kernel
theorem certified0222swap : Certified (graph core0222) (root 5) 3 0 :=
  of_native_maps core0222 DegreeOneSmallSpectrum178.graph DegreeOneSmallSpectrum182.graph
    sourceMap0222swap fusedMap0222swap sourceMap0222swap_checked fusedMap0222swap_checked
    DegreeOneSmallComparisons.comparison0222
#print axioms sourceMap0222swap_checked
#print axioms fusedMap0222swap_checked
#print axioms certified0222swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
