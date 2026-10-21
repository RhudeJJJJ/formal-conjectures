/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0110 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0110 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 4 3 3 v)
def fusedMap0110 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 3 3 v)
theorem sourceMap0110_checked : acceptsGraphIso
    (source (graph core0110) (root 4) 3 3) DegreeOneSmallSpectrum1508.graph sourceMap0110=true := by decide +kernel
theorem fusedMap0110_checked : acceptsGraphIso
    (fused (graph core0110) (root 4) 3 3) DegreeOneSmallSpectrum861.graph fusedMap0110=true := by decide +kernel
theorem certified0110 : Certified (graph core0110) (root 4) 3 3 :=
  of_native_maps core0110 DegreeOneSmallSpectrum1508.graph DegreeOneSmallSpectrum861.graph
    sourceMap0110 fusedMap0110 sourceMap0110_checked fusedMap0110_checked
    DegreeOneSmallComparisons.comparison0110
#print axioms sourceMap0110_checked
#print axioms fusedMap0110_checked
#print axioms certified0110
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
