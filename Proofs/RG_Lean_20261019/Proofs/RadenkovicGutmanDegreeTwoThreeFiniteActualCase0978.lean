/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0978 : Family 10 := level10.get ⟨1647,by decide⟩
def sourceMap0978 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0978 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0978_checked : acceptsGraphIso
    (source (graph core0978) (root 10) 0 0) DegreeOneSmallSpectrum2008.graph sourceMap0978=true := by decide +kernel
theorem fusedMap0978_checked : acceptsGraphIso
    (fused (graph core0978) (root 10) 0 0) DegreeOneSmallSpectrum1776.graph fusedMap0978=true := by decide +kernel
theorem certified0978 : Certified (graph core0978) (root 10) 0 0 :=
  of_native_maps core0978 DegreeOneSmallSpectrum2008.graph DegreeOneSmallSpectrum1776.graph
    sourceMap0978 fusedMap0978 sourceMap0978_checked fusedMap0978_checked
    DegreeTwoThreeFiniteComparisons.comparison0978
#print axioms sourceMap0978_checked
#print axioms fusedMap0978_checked
#print axioms certified0978
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
