/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0982 : Family 8 := level8.get ⟨87,by decide⟩
def sourceMap0982 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,6,7,8,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0982 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0982_checked : acceptsGraphIso
    (source (graph core0982) (root 8) 1 1) DegreeOneSmallSpectrum1320.graph sourceMap0982=true := by decide +kernel
theorem fusedMap0982_checked : acceptsGraphIso
    (fused (graph core0982) (root 8) 1 1) DegreeOneSmallSpectrum972.graph fusedMap0982=true := by decide +kernel
theorem certified0982 : Certified (graph core0982) (root 8) 1 1 :=
  of_native_maps core0982 DegreeOneSmallSpectrum1320.graph DegreeOneSmallSpectrum972.graph
    sourceMap0982 fusedMap0982 sourceMap0982_checked fusedMap0982_checked
    DegreeOneSmallComparisons.comparison0982
#print axioms sourceMap0982_checked
#print axioms fusedMap0982_checked
#print axioms certified0982
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
