/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0971 : Family 8 := level8.get ⟨84,by decide⟩
def sourceMap0971 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,5,6,7,3,4] (sourceLabel 8 0 0 v)
def fusedMap0971 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0971_checked : acceptsGraphIso
    (source (graph core0971) (root 8) 0 0) DegreeOneSmallSpectrum270.graph sourceMap0971=true := by decide +kernel
theorem fusedMap0971_checked : acceptsGraphIso
    (fused (graph core0971) (root 8) 0 0) DegreeOneSmallSpectrum219.graph fusedMap0971=true := by decide +kernel
theorem certified0971 : Certified (graph core0971) (root 8) 0 0 :=
  of_native_maps core0971 DegreeOneSmallSpectrum270.graph DegreeOneSmallSpectrum219.graph
    sourceMap0971 fusedMap0971 sourceMap0971_checked fusedMap0971_checked
    DegreeOneSmallComparisons.comparison0971
#print axioms sourceMap0971_checked
#print axioms fusedMap0971_checked
#print axioms certified0971
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
