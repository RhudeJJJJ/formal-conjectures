/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0790 : Family 8 := level8.get ⟨15,by decide⟩
def sourceMap0790 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0790 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0790_checked : acceptsGraphIso
    (source (graph core0790) (root 8) 1 1) DegreeOneSmallSpectrum1335.graph sourceMap0790=true := by decide +kernel
theorem fusedMap0790_checked : acceptsGraphIso
    (fused (graph core0790) (root 8) 1 1) DegreeOneSmallSpectrum922.graph fusedMap0790=true := by decide +kernel
theorem certified0790 : Certified (graph core0790) (root 8) 1 1 :=
  of_native_maps core0790 DegreeOneSmallSpectrum1335.graph DegreeOneSmallSpectrum922.graph
    sourceMap0790 fusedMap0790 sourceMap0790_checked fusedMap0790_checked
    DegreeOneSmallComparisons.comparison0790
#print axioms sourceMap0790_checked
#print axioms fusedMap0790_checked
#print axioms certified0790
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
