/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0957 : Family 10 := level10.get ⟨1592,by decide⟩
def sourceMap0957 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0957 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0957_checked : acceptsGraphIso
    (source (graph core0957) (root 10) 0 0) DegreeOneSmallSpectrum1665.graph sourceMap0957=true := by decide +kernel
theorem fusedMap0957_checked : acceptsGraphIso
    (fused (graph core0957) (root 10) 0 0) DegreeOneSmallSpectrum1664.graph fusedMap0957=true := by decide +kernel
theorem certified0957 : Certified (graph core0957) (root 10) 0 0 :=
  of_native_maps core0957 DegreeOneSmallSpectrum1665.graph DegreeOneSmallSpectrum1664.graph
    sourceMap0957 fusedMap0957 sourceMap0957_checked fusedMap0957_checked
    DegreeTwoThreeFiniteComparisons.comparison0957
#print axioms sourceMap0957_checked
#print axioms fusedMap0957_checked
#print axioms certified0957
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
