/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0994 : Family 8 := level8.get ⟨97,by decide⟩
def sourceMap0994 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0994 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0994_checked : acceptsGraphIso
    (source (graph core0994) (root 8) 1 1) DegreeOneSmallSpectrum1594.graph sourceMap0994=true := by decide +kernel
theorem fusedMap0994_checked : acceptsGraphIso
    (fused (graph core0994) (root 8) 1 1) DegreeOneSmallSpectrum998.graph fusedMap0994=true := by decide +kernel
theorem certified0994 : Certified (graph core0994) (root 8) 1 1 :=
  of_native_maps core0994 DegreeOneSmallSpectrum1594.graph DegreeOneSmallSpectrum998.graph
    sourceMap0994 fusedMap0994 sourceMap0994_checked fusedMap0994_checked
    DegreeOneSmallComparisons.comparison0994
#print axioms sourceMap0994_checked
#print axioms fusedMap0994_checked
#print axioms certified0994
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
