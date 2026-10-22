/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0198 : Family 9 := level9.get ⟨154,by decide⟩
def sourceMap0198 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0198 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0198_checked : acceptsGraphIso
    (source (graph core0198) (root 9) 0 0) DegreeTwoThreeSpectrum370.graph sourceMap0198=true := by decide +kernel
theorem fusedMap0198_checked : acceptsGraphIso
    (fused (graph core0198) (root 9) 0 0) DegreeOneSmallSpectrum421.graph fusedMap0198=true := by decide +kernel
theorem certified0198 : Certified (graph core0198) (root 9) 0 0 :=
  of_native_maps core0198 DegreeTwoThreeSpectrum370.graph DegreeOneSmallSpectrum421.graph
    sourceMap0198 fusedMap0198 sourceMap0198_checked fusedMap0198_checked
    DegreeTwoThreeFiniteComparisons.comparison0198
#print axioms sourceMap0198_checked
#print axioms fusedMap0198_checked
#print axioms certified0198
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
