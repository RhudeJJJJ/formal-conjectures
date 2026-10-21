/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0981 : Family 8 := level8.get ⟨87,by decide⟩
def sourceMap0981 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0981 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0981_checked : acceptsGraphIso
    (source (graph core0981) (root 8) 0 2) DegreeOneSmallSpectrum1507.graph sourceMap0981=true := by decide +kernel
theorem fusedMap0981_checked : acceptsGraphIso
    (fused (graph core0981) (root 8) 0 2) DegreeOneSmallSpectrum972.graph fusedMap0981=true := by decide +kernel
theorem certified0981 : Certified (graph core0981) (root 8) 0 2 :=
  of_native_maps core0981 DegreeOneSmallSpectrum1507.graph DegreeOneSmallSpectrum972.graph
    sourceMap0981 fusedMap0981 sourceMap0981_checked fusedMap0981_checked
    DegreeOneSmallComparisons.comparison0981
#print axioms sourceMap0981_checked
#print axioms fusedMap0981_checked
#print axioms certified0981
def sourceMap0981swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0981swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0981swap_checked : acceptsGraphIso
    (source (graph core0981) (root 8) 2 0) DegreeOneSmallSpectrum1507.graph sourceMap0981swap=true := by decide +kernel
theorem fusedMap0981swap_checked : acceptsGraphIso
    (fused (graph core0981) (root 8) 2 0) DegreeOneSmallSpectrum972.graph fusedMap0981swap=true := by decide +kernel
theorem certified0981swap : Certified (graph core0981) (root 8) 2 0 :=
  of_native_maps core0981 DegreeOneSmallSpectrum1507.graph DegreeOneSmallSpectrum972.graph
    sourceMap0981swap fusedMap0981swap sourceMap0981swap_checked fusedMap0981swap_checked
    DegreeOneSmallComparisons.comparison0981
#print axioms sourceMap0981swap_checked
#print axioms fusedMap0981swap_checked
#print axioms certified0981swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
