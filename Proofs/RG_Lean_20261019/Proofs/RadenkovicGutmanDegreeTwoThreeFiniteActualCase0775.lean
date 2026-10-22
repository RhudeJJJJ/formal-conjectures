/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0775 : Family 10 := level10.get ⟨1155,by decide⟩
def sourceMap0775 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0775 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0775_checked : acceptsGraphIso
    (source (graph core0775) (root 10) 0 0) DegreeOneSmallSpectrum1625.graph sourceMap0775=true := by decide +kernel
theorem fusedMap0775_checked : acceptsGraphIso
    (fused (graph core0775) (root 10) 0 0) DegreeOneSmallSpectrum1831.graph fusedMap0775=true := by decide +kernel
theorem certified0775 : Certified (graph core0775) (root 10) 0 0 :=
  of_native_maps core0775 DegreeOneSmallSpectrum1625.graph DegreeOneSmallSpectrum1831.graph
    sourceMap0775 fusedMap0775 sourceMap0775_checked fusedMap0775_checked
    DegreeTwoThreeFiniteComparisons.comparison0775
#print axioms sourceMap0775_checked
#print axioms fusedMap0775_checked
#print axioms certified0775
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
