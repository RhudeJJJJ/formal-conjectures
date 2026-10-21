/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0234 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0234 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap0234 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0234_checked : acceptsGraphIso
    (source (graph core0234) (root 5) 0 3) DegreeOneSmallSpectrum199.graph sourceMap0234=true := by decide +kernel
theorem fusedMap0234_checked : acceptsGraphIso
    (fused (graph core0234) (root 5) 0 3) DegreeOneSmallSpectrum202.graph fusedMap0234=true := by decide +kernel
theorem certified0234 : Certified (graph core0234) (root 5) 0 3 :=
  of_native_maps core0234 DegreeOneSmallSpectrum199.graph DegreeOneSmallSpectrum202.graph
    sourceMap0234 fusedMap0234 sourceMap0234_checked fusedMap0234_checked
    DegreeOneSmallComparisons.comparison0234
#print axioms sourceMap0234_checked
#print axioms fusedMap0234_checked
#print axioms certified0234
def sourceMap0234swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,6] (sourceLabel 5 3 0 v)
def fusedMap0234swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0234swap_checked : acceptsGraphIso
    (source (graph core0234) (root 5) 3 0) DegreeOneSmallSpectrum199.graph sourceMap0234swap=true := by decide +kernel
theorem fusedMap0234swap_checked : acceptsGraphIso
    (fused (graph core0234) (root 5) 3 0) DegreeOneSmallSpectrum202.graph fusedMap0234swap=true := by decide +kernel
theorem certified0234swap : Certified (graph core0234) (root 5) 3 0 :=
  of_native_maps core0234 DegreeOneSmallSpectrum199.graph DegreeOneSmallSpectrum202.graph
    sourceMap0234swap fusedMap0234swap sourceMap0234swap_checked fusedMap0234swap_checked
    DegreeOneSmallComparisons.comparison0234
#print axioms sourceMap0234swap_checked
#print axioms fusedMap0234swap_checked
#print axioms certified0234swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
