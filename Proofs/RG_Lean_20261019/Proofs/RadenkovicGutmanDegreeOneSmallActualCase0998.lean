/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0998 : Family 8 := level8.get ⟨99,by decide⟩
def sourceMap0998 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0998 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0998_checked : acceptsGraphIso
    (source (graph core0998) (root 8) 1 1) DegreeOneSmallSpectrum1634.graph sourceMap0998=true := by decide +kernel
theorem fusedMap0998_checked : acceptsGraphIso
    (fused (graph core0998) (root 8) 1 1) DegreeOneSmallSpectrum1015.graph fusedMap0998=true := by decide +kernel
theorem certified0998 : Certified (graph core0998) (root 8) 1 1 :=
  of_native_maps core0998 DegreeOneSmallSpectrum1634.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0998 fusedMap0998 sourceMap0998_checked fusedMap0998_checked
    DegreeOneSmallComparisons.comparison0998
#print axioms sourceMap0998_checked
#print axioms fusedMap0998_checked
#print axioms certified0998
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
