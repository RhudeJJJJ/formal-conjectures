/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0241 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0241 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 2 2 v)
def fusedMap0241 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap0241_checked : acceptsGraphIso
    (source (graph core0241) (root 5) 2 2) DegreeOneSmallSpectrum794.graph sourceMap0241=true := by decide +kernel
theorem fusedMap0241_checked : acceptsGraphIso
    (fused (graph core0241) (root 5) 2 2) DegreeOneSmallSpectrum379.graph fusedMap0241=true := by decide +kernel
theorem certified0241 : Certified (graph core0241) (root 5) 2 2 :=
  of_native_maps core0241 DegreeOneSmallSpectrum794.graph DegreeOneSmallSpectrum379.graph
    sourceMap0241 fusedMap0241 sourceMap0241_checked fusedMap0241_checked
    DegreeOneSmallComparisons.comparison0241
#print axioms sourceMap0241_checked
#print axioms fusedMap0241_checked
#print axioms certified0241
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
