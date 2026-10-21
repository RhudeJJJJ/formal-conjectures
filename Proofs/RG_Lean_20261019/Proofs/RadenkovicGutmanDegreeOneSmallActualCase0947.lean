/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0947 : Family 8 := level8.get ⟨73,by decide⟩
def sourceMap0947 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0947 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0947_checked : acceptsGraphIso
    (source (graph core0947) (root 8) 0 0) DegreeOneSmallSpectrum299.graph sourceMap0947=true := by decide +kernel
theorem fusedMap0947_checked : acceptsGraphIso
    (fused (graph core0947) (root 8) 0 0) DegreeOneSmallSpectrum221.graph fusedMap0947=true := by decide +kernel
theorem certified0947 : Certified (graph core0947) (root 8) 0 0 :=
  of_native_maps core0947 DegreeOneSmallSpectrum299.graph DegreeOneSmallSpectrum221.graph
    sourceMap0947 fusedMap0947 sourceMap0947_checked fusedMap0947_checked
    DegreeOneSmallComparisons.comparison0947
#print axioms sourceMap0947_checked
#print axioms fusedMap0947_checked
#print axioms certified0947
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
