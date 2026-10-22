/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0174 : Family 9 := level9.get ⟨73,by decide⟩
def sourceMap0174 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0174 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0174_checked : acceptsGraphIso
    (source (graph core0174) (root 9) 0 0) DegreeOneSmallSpectrum421.graph sourceMap0174=true := by decide +kernel
theorem fusedMap0174_checked : acceptsGraphIso
    (fused (graph core0174) (root 9) 0 0) DegreeOneSmallSpectrum514.graph fusedMap0174=true := by decide +kernel
theorem certified0174 : Certified (graph core0174) (root 9) 0 0 :=
  of_native_maps core0174 DegreeOneSmallSpectrum421.graph DegreeOneSmallSpectrum514.graph
    sourceMap0174 fusedMap0174 sourceMap0174_checked fusedMap0174_checked
    DegreeTwoThreeFiniteComparisons.comparison0174
#print axioms sourceMap0174_checked
#print axioms fusedMap0174_checked
#print axioms certified0174
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
