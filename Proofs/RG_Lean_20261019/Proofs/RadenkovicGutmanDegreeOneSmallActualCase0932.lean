/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0932 : Family 8 := level8.get ⟨66,by decide⟩
def sourceMap0932 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0932 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 0 1 v)
theorem sourceMap0932_checked : acceptsGraphIso
    (source (graph core0932) (root 8) 0 1) DegreeOneSmallSpectrum542.graph sourceMap0932=true := by decide +kernel
theorem fusedMap0932_checked : acceptsGraphIso
    (fused (graph core0932) (root 8) 0 1) DegreeOneSmallSpectrum560.graph fusedMap0932=true := by decide +kernel
theorem certified0932 : Certified (graph core0932) (root 8) 0 1 :=
  of_native_maps core0932 DegreeOneSmallSpectrum542.graph DegreeOneSmallSpectrum560.graph
    sourceMap0932 fusedMap0932 sourceMap0932_checked fusedMap0932_checked
    DegreeOneSmallComparisons.comparison0932
#print axioms sourceMap0932_checked
#print axioms fusedMap0932_checked
#print axioms certified0932
def sourceMap0932swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0932swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (fusedLabel 8 1 0 v)
theorem sourceMap0932swap_checked : acceptsGraphIso
    (source (graph core0932) (root 8) 1 0) DegreeOneSmallSpectrum542.graph sourceMap0932swap=true := by decide +kernel
theorem fusedMap0932swap_checked : acceptsGraphIso
    (fused (graph core0932) (root 8) 1 0) DegreeOneSmallSpectrum560.graph fusedMap0932swap=true := by decide +kernel
theorem certified0932swap : Certified (graph core0932) (root 8) 1 0 :=
  of_native_maps core0932 DegreeOneSmallSpectrum542.graph DegreeOneSmallSpectrum560.graph
    sourceMap0932swap fusedMap0932swap sourceMap0932swap_checked fusedMap0932swap_checked
    DegreeOneSmallComparisons.comparison0932
#print axioms sourceMap0932swap_checked
#print axioms fusedMap0932swap_checked
#print axioms certified0932swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
