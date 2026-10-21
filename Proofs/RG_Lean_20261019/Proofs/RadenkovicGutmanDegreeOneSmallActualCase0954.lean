/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0954 : Family 8 := level8.get ⟨75,by decide⟩
def sourceMap0954 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0954 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0954_checked : acceptsGraphIso
    (source (graph core0954) (root 8) 1 1) DegreeOneSmallSpectrum1344.graph sourceMap0954=true := by decide +kernel
theorem fusedMap0954_checked : acceptsGraphIso
    (fused (graph core0954) (root 8) 1 1) DegreeOneSmallSpectrum952.graph fusedMap0954=true := by decide +kernel
theorem certified0954 : Certified (graph core0954) (root 8) 1 1 :=
  of_native_maps core0954 DegreeOneSmallSpectrum1344.graph DegreeOneSmallSpectrum952.graph
    sourceMap0954 fusedMap0954 sourceMap0954_checked fusedMap0954_checked
    DegreeOneSmallComparisons.comparison0954
#print axioms sourceMap0954_checked
#print axioms fusedMap0954_checked
#print axioms certified0954
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
