/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0973 : Family 10 := level10.get ⟨1634,by decide⟩
def sourceMap0973 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0973 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0973_checked : acceptsGraphIso
    (source (graph core0973) (root 10) 0 0) DegreeOneSmallSpectrum1754.graph sourceMap0973=true := by decide +kernel
theorem fusedMap0973_checked : acceptsGraphIso
    (fused (graph core0973) (root 10) 0 0) DegreeOneSmallSpectrum1753.graph fusedMap0973=true := by decide +kernel
theorem certified0973 : Certified (graph core0973) (root 10) 0 0 :=
  of_native_maps core0973 DegreeOneSmallSpectrum1754.graph DegreeOneSmallSpectrum1753.graph
    sourceMap0973 fusedMap0973 sourceMap0973_checked fusedMap0973_checked
    DegreeTwoThreeFiniteComparisons.comparison0973
#print axioms sourceMap0973_checked
#print axioms fusedMap0973_checked
#print axioms certified0973
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
