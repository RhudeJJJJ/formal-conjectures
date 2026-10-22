/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0965 : Family 10 := level10.get ⟨1618,by decide⟩
def sourceMap0965 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0965 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0965_checked : acceptsGraphIso
    (source (graph core0965) (root 10) 0 0) DegreeOneSmallSpectrum2005.graph sourceMap0965=true := by decide +kernel
theorem fusedMap0965_checked : acceptsGraphIso
    (fused (graph core0965) (root 10) 0 0) DegreeOneSmallSpectrum1704.graph fusedMap0965=true := by decide +kernel
theorem certified0965 : Certified (graph core0965) (root 10) 0 0 :=
  of_native_maps core0965 DegreeOneSmallSpectrum2005.graph DegreeOneSmallSpectrum1704.graph
    sourceMap0965 fusedMap0965 sourceMap0965_checked fusedMap0965_checked
    DegreeTwoThreeFiniteComparisons.comparison0965
#print axioms sourceMap0965_checked
#print axioms fusedMap0965_checked
#print axioms certified0965
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
