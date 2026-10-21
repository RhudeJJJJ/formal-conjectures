/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0238 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0238 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0238 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0238_checked : acceptsGraphIso
    (source (graph core0238) (root 5) 1 2) DegreeOneSmallSpectrum329.graph sourceMap0238=true := by decide +kernel
theorem fusedMap0238_checked : acceptsGraphIso
    (fused (graph core0238) (root 5) 1 2) DegreeOneSmallSpectrum202.graph fusedMap0238=true := by decide +kernel
theorem certified0238 : Certified (graph core0238) (root 5) 1 2 :=
  of_native_maps core0238 DegreeOneSmallSpectrum329.graph DegreeOneSmallSpectrum202.graph
    sourceMap0238 fusedMap0238 sourceMap0238_checked fusedMap0238_checked
    DegreeOneSmallComparisons.comparison0238
#print axioms sourceMap0238_checked
#print axioms fusedMap0238_checked
#print axioms certified0238
def sourceMap0238swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0238swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0238swap_checked : acceptsGraphIso
    (source (graph core0238) (root 5) 2 1) DegreeOneSmallSpectrum329.graph sourceMap0238swap=true := by decide +kernel
theorem fusedMap0238swap_checked : acceptsGraphIso
    (fused (graph core0238) (root 5) 2 1) DegreeOneSmallSpectrum202.graph fusedMap0238swap=true := by decide +kernel
theorem certified0238swap : Certified (graph core0238) (root 5) 2 1 :=
  of_native_maps core0238 DegreeOneSmallSpectrum329.graph DegreeOneSmallSpectrum202.graph
    sourceMap0238swap fusedMap0238swap sourceMap0238swap_checked fusedMap0238swap_checked
    DegreeOneSmallComparisons.comparison0238
#print axioms sourceMap0238swap_checked
#print axioms fusedMap0238swap_checked
#print axioms certified0238swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
