/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0987 : Family 8 := level8.get ⟨96,by decide⟩
def sourceMap0987 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0987 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0987_checked : acceptsGraphIso
    (source (graph core0987) (root 8) 0 0) DegreeOneSmallSpectrum237.graph sourceMap0987=true := by decide +kernel
theorem fusedMap0987_checked : acceptsGraphIso
    (fused (graph core0987) (root 8) 0 0) DegreeOneSmallSpectrum239.graph fusedMap0987=true := by decide +kernel
theorem certified0987 : Certified (graph core0987) (root 8) 0 0 :=
  of_native_maps core0987 DegreeOneSmallSpectrum237.graph DegreeOneSmallSpectrum239.graph
    sourceMap0987 fusedMap0987 sourceMap0987_checked fusedMap0987_checked
    DegreeOneSmallComparisons.comparison0987
#print axioms sourceMap0987_checked
#print axioms fusedMap0987_checked
#print axioms certified0987
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
