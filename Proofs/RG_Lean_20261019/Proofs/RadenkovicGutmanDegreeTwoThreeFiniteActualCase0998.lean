/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0998 : Family 10 := level10.get ⟨1711,by decide⟩
def sourceMap0998 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0998 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0998_checked : acceptsGraphIso
    (source (graph core0998) (root 10) 0 0) DegreeTwoThreeSpectrum1603.graph sourceMap0998=true := by decide +kernel
theorem fusedMap0998_checked : acceptsGraphIso
    (fused (graph core0998) (root 10) 0 0) DegreeOneSmallSpectrum1901.graph fusedMap0998=true := by decide +kernel
theorem certified0998 : Certified (graph core0998) (root 10) 0 0 :=
  of_native_maps core0998 DegreeTwoThreeSpectrum1603.graph DegreeOneSmallSpectrum1901.graph
    sourceMap0998 fusedMap0998 sourceMap0998_checked fusedMap0998_checked
    DegreeTwoThreeFiniteComparisons.comparison0998
#print axioms sourceMap0998_checked
#print axioms fusedMap0998_checked
#print axioms certified0998
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
