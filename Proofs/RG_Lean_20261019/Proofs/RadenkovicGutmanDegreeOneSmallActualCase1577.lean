/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1577 : Family 9 := level9.get ⟨321,by decide⟩
def sourceMap1577 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1577 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1577_checked : acceptsGraphIso
    (source (graph core1577) (root 9) 0 0) DegreeOneSmallSpectrum606.graph sourceMap1577=true := by decide +kernel
theorem fusedMap1577_checked : acceptsGraphIso
    (fused (graph core1577) (root 9) 0 0) DegreeOneSmallSpectrum608.graph fusedMap1577=true := by decide +kernel
theorem certified1577 : Certified (graph core1577) (root 9) 0 0 :=
  of_native_maps core1577 DegreeOneSmallSpectrum606.graph DegreeOneSmallSpectrum608.graph
    sourceMap1577 fusedMap1577 sourceMap1577_checked fusedMap1577_checked
    DegreeOneSmallComparisons.comparison1577
#print axioms sourceMap1577_checked
#print axioms fusedMap1577_checked
#print axioms certified1577
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
