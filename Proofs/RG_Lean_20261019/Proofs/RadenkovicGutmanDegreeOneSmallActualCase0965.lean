/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0965 : Family 8 := level8.get ⟨79,by decide⟩
def sourceMap0965 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0965 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0965_checked : acceptsGraphIso
    (source (graph core0965) (root 8) 0 2) DegreeOneSmallSpectrum1503.graph sourceMap0965=true := by decide +kernel
theorem fusedMap0965_checked : acceptsGraphIso
    (fused (graph core0965) (root 8) 0 2) DegreeOneSmallSpectrum958.graph fusedMap0965=true := by decide +kernel
theorem certified0965 : Certified (graph core0965) (root 8) 0 2 :=
  of_native_maps core0965 DegreeOneSmallSpectrum1503.graph DegreeOneSmallSpectrum958.graph
    sourceMap0965 fusedMap0965 sourceMap0965_checked fusedMap0965_checked
    DegreeOneSmallComparisons.comparison0965
#print axioms sourceMap0965_checked
#print axioms fusedMap0965_checked
#print axioms certified0965
def sourceMap0965swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0965swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0965swap_checked : acceptsGraphIso
    (source (graph core0965) (root 8) 2 0) DegreeOneSmallSpectrum1503.graph sourceMap0965swap=true := by decide +kernel
theorem fusedMap0965swap_checked : acceptsGraphIso
    (fused (graph core0965) (root 8) 2 0) DegreeOneSmallSpectrum958.graph fusedMap0965swap=true := by decide +kernel
theorem certified0965swap : Certified (graph core0965) (root 8) 2 0 :=
  of_native_maps core0965 DegreeOneSmallSpectrum1503.graph DegreeOneSmallSpectrum958.graph
    sourceMap0965swap fusedMap0965swap sourceMap0965swap_checked fusedMap0965swap_checked
    DegreeOneSmallComparisons.comparison0965
#print axioms sourceMap0965swap_checked
#print axioms fusedMap0965swap_checked
#print axioms certified0965swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
