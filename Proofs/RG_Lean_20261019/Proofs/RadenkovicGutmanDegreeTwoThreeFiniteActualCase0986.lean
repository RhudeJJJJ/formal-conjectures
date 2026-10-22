/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0986 : Family 10 := level10.get ⟨1664,by decide⟩
def sourceMap0986 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0986 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0986_checked : acceptsGraphIso
    (source (graph core0986) (root 10) 0 0) DegreeOneSmallSpectrum1823.graph sourceMap0986=true := by decide +kernel
theorem fusedMap0986_checked : acceptsGraphIso
    (fused (graph core0986) (root 10) 0 0) DegreeOneSmallSpectrum1822.graph fusedMap0986=true := by decide +kernel
theorem certified0986 : Certified (graph core0986) (root 10) 0 0 :=
  of_native_maps core0986 DegreeOneSmallSpectrum1823.graph DegreeOneSmallSpectrum1822.graph
    sourceMap0986 fusedMap0986 sourceMap0986_checked fusedMap0986_checked
    DegreeTwoThreeFiniteComparisons.comparison0986
#print axioms sourceMap0986_checked
#print axioms fusedMap0986_checked
#print axioms certified0986
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
