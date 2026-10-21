/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0091 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0091 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11] (sourceLabel 3 2 4 v)
def fusedMap0091 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 2 4 v)
theorem sourceMap0091_checked : acceptsGraphIso
    (source (graph core0091) (root 3) 2 4) DegreeOneSmallSpectrum567.graph sourceMap0091=true := by decide +kernel
theorem fusedMap0091_checked : acceptsGraphIso
    (fused (graph core0091) (root 3) 2 4) DegreeOneSmallSpectrum378.graph fusedMap0091=true := by decide +kernel
theorem certified0091 : Certified (graph core0091) (root 3) 2 4 :=
  of_native_maps core0091 DegreeOneSmallSpectrum567.graph DegreeOneSmallSpectrum378.graph
    sourceMap0091 fusedMap0091 sourceMap0091_checked fusedMap0091_checked
    DegreeOneSmallComparisons.comparison0091
#print axioms sourceMap0091_checked
#print axioms fusedMap0091_checked
#print axioms certified0091
def sourceMap0091swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,5,6,7,0,8,9,10,11,2,3,4] (sourceLabel 3 4 2 v)
def fusedMap0091swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 4 2 v)
theorem sourceMap0091swap_checked : acceptsGraphIso
    (source (graph core0091) (root 3) 4 2) DegreeOneSmallSpectrum567.graph sourceMap0091swap=true := by decide +kernel
theorem fusedMap0091swap_checked : acceptsGraphIso
    (fused (graph core0091) (root 3) 4 2) DegreeOneSmallSpectrum378.graph fusedMap0091swap=true := by decide +kernel
theorem certified0091swap : Certified (graph core0091) (root 3) 4 2 :=
  of_native_maps core0091 DegreeOneSmallSpectrum567.graph DegreeOneSmallSpectrum378.graph
    sourceMap0091swap fusedMap0091swap sourceMap0091swap_checked fusedMap0091swap_checked
    DegreeOneSmallComparisons.comparison0091
#print axioms sourceMap0091swap_checked
#print axioms fusedMap0091swap_checked
#print axioms certified0091swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
