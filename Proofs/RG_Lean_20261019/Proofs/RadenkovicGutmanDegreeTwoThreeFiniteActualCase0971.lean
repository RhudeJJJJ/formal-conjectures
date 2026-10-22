/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0971 : Family 10 := level10.get ⟨1631,by decide⟩
def sourceMap0971 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0971 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0971_checked : acceptsGraphIso
    (source (graph core0971) (root 10) 0 0) DegreeOneSmallSpectrum2007.graph sourceMap0971=true := by decide +kernel
theorem fusedMap0971_checked : acceptsGraphIso
    (fused (graph core0971) (root 10) 0 0) DegreeOneSmallSpectrum1736.graph fusedMap0971=true := by decide +kernel
theorem certified0971 : Certified (graph core0971) (root 10) 0 0 :=
  of_native_maps core0971 DegreeOneSmallSpectrum2007.graph DegreeOneSmallSpectrum1736.graph
    sourceMap0971 fusedMap0971 sourceMap0971_checked fusedMap0971_checked
    DegreeTwoThreeFiniteComparisons.comparison0971
#print axioms sourceMap0971_checked
#print axioms fusedMap0971_checked
#print axioms certified0971
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
