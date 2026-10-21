/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0989 : Family 8 := level8.get ⟨96,by decide⟩
def sourceMap0989 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0989 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0989_checked : acceptsGraphIso
    (source (graph core0989) (root 8) 0 2) DegreeOneSmallSpectrum991.graph sourceMap0989=true := by decide +kernel
theorem fusedMap0989_checked : acceptsGraphIso
    (fused (graph core0989) (root 8) 0 2) DegreeOneSmallSpectrum992.graph fusedMap0989=true := by decide +kernel
theorem certified0989 : Certified (graph core0989) (root 8) 0 2 :=
  of_native_maps core0989 DegreeOneSmallSpectrum991.graph DegreeOneSmallSpectrum992.graph
    sourceMap0989 fusedMap0989 sourceMap0989_checked fusedMap0989_checked
    DegreeOneSmallComparisons.comparison0989
#print axioms sourceMap0989_checked
#print axioms fusedMap0989_checked
#print axioms certified0989
def sourceMap0989swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0989swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0989swap_checked : acceptsGraphIso
    (source (graph core0989) (root 8) 2 0) DegreeOneSmallSpectrum991.graph sourceMap0989swap=true := by decide +kernel
theorem fusedMap0989swap_checked : acceptsGraphIso
    (fused (graph core0989) (root 8) 2 0) DegreeOneSmallSpectrum992.graph fusedMap0989swap=true := by decide +kernel
theorem certified0989swap : Certified (graph core0989) (root 8) 2 0 :=
  of_native_maps core0989 DegreeOneSmallSpectrum991.graph DegreeOneSmallSpectrum992.graph
    sourceMap0989swap fusedMap0989swap sourceMap0989swap_checked fusedMap0989swap_checked
    DegreeOneSmallComparisons.comparison0989
#print axioms sourceMap0989swap_checked
#print axioms fusedMap0989swap_checked
#print axioms certified0989swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
