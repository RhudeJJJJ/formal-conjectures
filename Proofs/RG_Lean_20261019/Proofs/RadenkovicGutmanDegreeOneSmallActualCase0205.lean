/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0205 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0205 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap0205 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0205_checked : acceptsGraphIso
    (source (graph core0205) (root 5) 2 2) DegreeOneSmallSpectrum562.graph sourceMap0205=true := by decide +kernel
theorem fusedMap0205_checked : acceptsGraphIso
    (fused (graph core0205) (root 5) 2 2) DegreeOneSmallSpectrum392.graph fusedMap0205=true := by decide +kernel
theorem certified0205 : Certified (graph core0205) (root 5) 2 2 :=
  of_native_maps core0205 DegreeOneSmallSpectrum562.graph DegreeOneSmallSpectrum392.graph
    sourceMap0205 fusedMap0205 sourceMap0205_checked fusedMap0205_checked
    DegreeOneSmallComparisons.comparison0205
#print axioms sourceMap0205_checked
#print axioms fusedMap0205_checked
#print axioms certified0205
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
