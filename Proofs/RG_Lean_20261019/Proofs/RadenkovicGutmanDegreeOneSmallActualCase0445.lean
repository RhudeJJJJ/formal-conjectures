/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0445 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0445 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12] (sourceLabel 6 1 3 v)
def fusedMap0445 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0445_checked : acceptsGraphIso
    (source (graph core0445) (root 6) 1 3) DegreeOneSmallSpectrum1536.graph sourceMap0445=true := by decide +kernel
theorem fusedMap0445_checked : acceptsGraphIso
    (fused (graph core0445) (root 6) 1 3) DegreeOneSmallSpectrum985.graph fusedMap0445=true := by decide +kernel
theorem certified0445 : Certified (graph core0445) (root 6) 1 3 :=
  of_native_maps core0445 DegreeOneSmallSpectrum1536.graph DegreeOneSmallSpectrum985.graph
    sourceMap0445 fusedMap0445 sourceMap0445_checked fusedMap0445_checked
    DegreeOneSmallComparisons.comparison0445
#print axioms sourceMap0445_checked
#print axioms fusedMap0445_checked
#print axioms certified0445
def sourceMap0445swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,8,9] (sourceLabel 6 3 1 v)
def fusedMap0445swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0445swap_checked : acceptsGraphIso
    (source (graph core0445) (root 6) 3 1) DegreeOneSmallSpectrum1536.graph sourceMap0445swap=true := by decide +kernel
theorem fusedMap0445swap_checked : acceptsGraphIso
    (fused (graph core0445) (root 6) 3 1) DegreeOneSmallSpectrum985.graph fusedMap0445swap=true := by decide +kernel
theorem certified0445swap : Certified (graph core0445) (root 6) 3 1 :=
  of_native_maps core0445 DegreeOneSmallSpectrum1536.graph DegreeOneSmallSpectrum985.graph
    sourceMap0445swap fusedMap0445swap sourceMap0445swap_checked fusedMap0445swap_checked
    DegreeOneSmallComparisons.comparison0445
#print axioms sourceMap0445swap_checked
#print axioms fusedMap0445swap_checked
#print axioms certified0445swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
